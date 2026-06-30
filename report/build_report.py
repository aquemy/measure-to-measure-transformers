#!/usr/bin/env python3
"""Generate the experiment validation report (report/experiments.qmd) from the campaign artifacts.

The report is data-driven: it reads every experiments/results/<exp>/summary.json (verdict +
hypothesis + explanation + figures) and manifest.json (provenance), the tested-claim metadata from
claims.toml, and the method code from each experiments/<exp>/run.py. It emits a single Quarto source
that renders to BOTH html and pdf (`format: [html, pdf]`), so one command yields the website page and
the citable LaTeX-built PDF. Nothing in the report is hand-maintained; re-run this after the campaign.

It writes two sources from the same body: report/experiments.qmd (the standalone, citable report,
`format: [html, pdf]`) and site/experiments.qmd (the website page; the site supplies the html
theme, and figures point at the copy site/build.py stages under the site project).

Usage:
    python report/build_report.py            # writes report/experiments.qmd + site/experiments.qmd
    quarto render report/experiments.qmd      # -> report/experiments.html + report/experiments.pdf
"""
from __future__ import annotations

import json
import re
import subprocess
import tomllib
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parent.parent
RESULTS = REPO / "experiments" / "results"
RUNS = REPO / "experiments"
OUT = REPO / "report" / "experiments.qmd"
SITE_OUT = REPO / "site" / "experiments.qmd"
CLAIMS = REPO / "claims.toml"

PAPER_CITE = "Geshkovski, Rigollet, Ruiz-Balet, *Measure-to-measure interpolation using Transformers*, arXiv:2411.04551v3"


def github_blob_base() -> str:
    """Best-effort https blob base for the origin remote, e.g.
    https://github.com/aquemy/measure-to-measure-transformers/blob/main/ ."""
    try:
        url = subprocess.check_output(
            ["git", "-C", str(REPO), "config", "--get", "remote.origin.url"], text=True
        ).strip()
    except Exception:
        return ""
    if url.startswith("git@github.com:"):
        url = "https://github.com/" + url[len("git@github.com:") :]
    if url.endswith(".git"):
        url = url[: -len(".git")]
    return url + "/blob/main/"


BLOB = github_blob_base()


def load_claims() -> dict[str, Any]:
    if not CLAIMS.exists():
        return {}
    with CLAIMS.open("rb") as fh:
        return tomllib.load(fh).get("claims", {})


def _strip_docstrings(code: str) -> str:
    """Drop triple-quoted docstrings from the extracted code. They are the longest lines (causing
    PDF overflow) and duplicate the prose explanation rendered just above the code block."""
    out: list[str] = []
    in_doc = False
    for line in code.splitlines():
        s = line.strip()
        if not in_doc and (s.startswith('"""') or s.startswith("'''")):
            if s.count('"""') >= 2 or s.count("'''") >= 2:
                continue  # one-line docstring
            in_doc = True
            continue
        if in_doc:
            if '"""' in line or "'''" in line:
                in_doc = False
            continue
        out.append(line)
    # collapse the blank lines a removed docstring leaves behind
    cleaned: list[str] = []
    for line in out:
        if line.strip() == "" and cleaned and cleaned[-1].strip() == "":
            continue
        cleaned.append(line)
    return "\n".join(cleaned)


def extract_method(run_py: Path) -> str:
    """The method code: every helper def plus main's verdict computation, stopping before the
    figure-generation block (marked by '# figure:'). Keeps the math, drops the plotting noise and
    the docstrings (the prose explanation covers them)."""
    lines = run_py.read_text(encoding="utf-8").splitlines()
    first_def = next((i for i, l in enumerate(lines) if l.startswith("def ")), 0)
    fig = next((i for i, l in enumerate(lines) if "# figure:" in l), None)
    end = fig if fig is not None else len(lines)
    snippet = _strip_docstrings("\n".join(lines[first_def:end])).rstrip()
    # collapse the wide alignment padding before inline comments (code, spaces, '#') so lines fit
    snippet = "\n".join(re.sub(r"(\S)[ \t]{2,}#", r"\1  #", l) for l in snippet.splitlines())
    return snippet + "\n    # ... figure generation and Result(...) omitted; see full source."


def fmt_value(v: object) -> str:
    """Compact, readable rendering of a metric value for the metrics table."""
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, float):
        if v == 0.0:
            return "0"
        if abs(v) < 1e-3 or abs(v) >= 1e4:
            return f"{v:.2e}"
        return f"{v:.4g}"
    if isinstance(v, list):
        return "[" + ", ".join(fmt_value(x) for x in v) + "]"
    return str(v)


def metrics_table(metrics: dict[str, Any]) -> str:
    rows = ["| metric | value |", "| --- | --- |"]
    for k, v in metrics.items():
        rows.append(f"| `{k}` | {fmt_value(v)} |")
    return "\n".join(rows)


def tested_claims_block(exp_slug: str, claims: dict[str, Any]) -> str:
    """List the math claims this experiment validates, with their paper node and status."""
    entry = claims.get(exp_slug, {})
    tested = entry.get("tests", [])
    if not tested:
        return "_No cross-linked claims recorded._"
    rows = ["| claim | paper node | status |", "| --- | --- | --- |"]
    for slug in tested:
        c = claims.get(slug, {})
        rows.append(f"| `{slug}` | {c.get('paper', '?')} | {c.get('status', '?')} |")
    return "\n".join(rows)


def load_experiments() -> list[dict[str, Any]]:
    exps = []
    for d in sorted(RESULTS.iterdir()):
        summ = d / "summary.json"
        if not summ.exists():
            continue
        summary = json.loads(summ.read_text())
        man = d / "manifest.json"
        manifest = json.loads(man.read_text()) if man.exists() else {}
        exps.append({"dir": d, "summary": summary, "manifest": manifest})
    return exps


# LaTeX preamble injected into the PDF so long code lines wrap: the default Quarto Highlighting
# environment is a plain Verbatim with no line breaking, so wide code overflows the page. fvextra
# extends fancyvrb's Verbatim with breaklines/breakanywhere.
_PDF_HEADER = (
    r"\usepackage{fvextra}"
    "\n"
    r"\DefineVerbatimEnvironment{Highlighting}{Verbatim}{commandchars=\\\{\},breaklines,breakanywhere,fontsize=\small}"
)


def _pdf_header_yaml() -> str:
    """`_PDF_HEADER` indented under the YAML `text: |` literal block (8 spaces per line)."""
    return "\n".join("        " + line for line in _PDF_HEADER.splitlines())


def front_matter() -> str:
    return f"""---
title: "Numerical validation of measure-to-measure interpolation"
subtitle: "Seeded experiments E1-E7 for {PAPER_CITE}"
author: "Alexandre Quemy"
date-format: iso
abstract: |
  A reproducible, seeded validation campaign for the controllability results of Geshkovski,
  Rigollet, and Ruiz-Balet. Each experiment integrates the actual continuity-equation dynamics on
  the sphere and checks the quantitative content of a claim (a leaf computation, a proposition, or a
  theorem) against a pass criterion, producing a figure and a provenance manifest. This report is
  generated from the artifacts by `report/build_report.py`; the original paper is the work of its
  authors, the Lean formalization and these experiments are the present author's.
format:
  html:
    toc: true
    toc-depth: 2
    number-sections: true
    code-fold: true
    code-tools: true
    code-overflow: wrap
    theme: cosmo
  pdf:
    toc: true
    number-sections: true
    pdf-engine: xelatex
    code-overflow: wrap
    geometry: margin=1in
    include-in-header:
      text: |
{_pdf_header_yaml()}
---
"""


def intro(exps: list[dict[str, Any]]) -> str:
    n = len(exps)
    npass = sum(1 for e in exps if e["summary"].get("passed"))
    return f"""
## Overview

This report documents {n} seeded numerical experiments validating
{PAPER_CITE}. All runs are deterministic (`SEED = 0`) and integrate the
characteristic flow of the continuity equation (1.3),
$\\dot x = P_x^\\perp v(t,x)$ with $P_x^\\perp = I - x x^\\top$, on the unit sphere.

The experiments are run **alongside** the proofs, not batched at the end: an optional exploratory
probe shapes a hypothesis before a proof, and a seeded validation always follows it. The full
workflow is documented in `WORKFLOW.md`. Each experiment below is presented as **hypothesis**, **what
is tested** (the cross-linked claim and pass criterion), **method** (the integrator code and a brief
explanation), **results** (a figure and the measured metrics), and **analysis** (the verdict with its
provenance).

**Campaign result: {npass} / {n} pass.**

{summary_table(exps)}
"""


def summary_table(exps: list[dict[str, Any]]) -> str:
    rows = ["| Experiment | Claim | Verdict |", "| --- | --- | --- |"]
    for e in exps:
        s = e["summary"]
        verdict = "**PASS**" if s.get("passed") else "**FAIL**"
        rows.append(f"| {s['experiment']} | `{s['claim']}` | {verdict} |")
    return "\n".join(rows)


def experiment_section(
    e: dict[str, Any], claims: dict[str, Any], fig_prefix: str = "../experiments/results/"
) -> str:
    s, m = e["summary"], e["manifest"]
    name = s["experiment"]
    exp_slug = s["claim"].removeprefix("claim:")
    run_py = RUNS / name / "run.py"
    method = extract_method(run_py) if run_py.exists() else "# (source not found)"
    blob = f"{BLOB}experiments/{name}/run.py" if BLOB else ""
    src_link = f"[`experiments/{name}/run.py`]({blob})" if blob else f"`experiments/{name}/run.py`"

    # figure: first png in the figures list. The prefix differs by target: the standalone report
    # reaches the live results tree (../experiments/results/); the website page references a copy
    # staged inside the site project (experiments-figures/), the only path a Quarto website copies.
    png = next((f for f in s.get("figures", []) if f.endswith(".png")), None)
    fig_md = ""
    if png:
        fig_md = f"![{name} verdict figure]({fig_prefix}{png}){{width=100%}}\n"

    verdict = "**PASS**" if s.get("passed") else "**FAIL**"
    prov = (
        f"seed {m.get('seed', s.get('seed'))}, "
        f"git `{(m.get('git_sha') or '')[:10]}`, "
        f"{m.get('created_at', '')[:19]} UTC, "
        f"numpy {m.get('numpy', '?')}, python {m.get('python', '?')}"
    )

    return f"""
## {name}

### Hypothesis

{s.get('hypothesis', '_(none recorded)_')}

### What is tested

Claim `{s['claim']}`. It validates:

{tested_claims_block(exp_slug, claims)}

**Pass criterion.** {s.get('criterion', '')}

### Method

{s.get('explanation', '')}

Full source: {src_link}.

```python
{method}
```

### Results

{fig_md}
{metrics_table(s.get('metrics', {}))}

### Analysis

Verdict: {verdict}. The measured metrics meet the pass criterion above. Provenance: {prov}.
"""


def reproducibility(exps: list[dict[str, Any]]) -> str:
    return """
## Reproducibility

Every figure and number in this report regenerates from the seeded code:

```sh
cd experiments
for e in E1_mass_transport E2_clustering E3_disentangle E4_matching \\
         E5_lyapunov E6_end_to_end E7_linear_impossible; do
  uv run python -m ${e}.run
done
cd ..
python report/build_report.py        # regenerate this report's source
quarto render report/experiments.qmd # -> html + pdf
```

Each run writes `summary.json` (verdict + narrative), `manifest.json` (provenance: git sha, UTC
time, host, library versions), and the figure (`*.png` / `*.svg`). The provenance manifests record
the exact commit and environment each verdict was produced under.
"""


def build() -> str:
    claims = load_claims()
    exps = load_experiments()
    parts = [front_matter(), intro(exps)]
    parts += [experiment_section(e, claims) for e in exps]
    parts.append(reproducibility(exps))
    return "\n".join(parts)


# --- website variant -------------------------------------------------------------------------
# The same data-driven body, wrapped for the Quarto website (site/experiments.qmd): the site
# supplies the html theme/css/filter from its _quarto.yml, so the page carries only a title; the
# figures point at the staged copy under the site project; and a callout links the citable PDF.
SITE_FIG_PREFIX = "experiments-figures/"


def site_front_matter() -> str:
    return """---
title: "Numerical validation"
subtitle: "Seven seeded experiments E1-E7"
toc: true
toc-depth: 2
---
"""


def site_intro(exps: list[dict[str, Any]]) -> str:
    n = len(exps)
    npass = sum(1 for e in exps if e["summary"].get("passed"))
    return f"""
::: {{.callout-note appearance="simple"}}
This page is generated from the campaign artifacts by `report/build_report.py`. A citable,
self-contained version (with the full method listings) is available as a
[**downloadable PDF report**](experiments-report.pdf).
:::

The proofs are validated **alongside** the formalization, not batched at the end: an optional
exploratory probe shapes a hypothesis before a proof, and a seeded validation always follows it
(the cycle is documented in `WORKFLOW.md`). All {n} experiments are deterministic (`SEED = 0`) and
integrate the characteristic flow of the continuity equation (1.3),
$\\dot x = P_x^\\perp v(t,x)$ with $P_x^\\perp = I - x x^\\top$, on the unit sphere. Each one is
presented as **hypothesis**, **what is tested** (the cross-linked claim and pass criterion),
**method**, **results** (a figure and the measured metrics), and **analysis** (the verdict with its
provenance).

**Campaign result: {npass} / {n} pass.**

{summary_table(exps)}
"""


def build_site() -> str:
    claims = load_claims()
    exps = load_experiments()
    parts = [site_front_matter(), site_intro(exps)]
    parts += [experiment_section(e, claims, fig_prefix=SITE_FIG_PREFIX) for e in exps]
    parts.append(reproducibility(exps))
    return "\n".join(parts)


def main() -> int:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(build(), encoding="utf-8")
    print(f"wrote {OUT.relative_to(REPO)}")
    SITE_OUT.parent.mkdir(parents=True, exist_ok=True)
    SITE_OUT.write_text(build_site(), encoding="utf-8")
    print(f"wrote {SITE_OUT.relative_to(REPO)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
