#!/usr/bin/env python3
"""Assemble the whole website into ``docs/`` for classic GitHub Pages (no Actions).

One command regenerates every derived artifact and renders the Quarto site:

  1. the ClaimGraph (``claimgraph.json``) from the git history;
  2. the interactive viewer (``docs/claimgraph-viewer.html``) and the compact history timeline
     (``docs/history-timeline.html``), both self-contained, embedded by ``claimgraph.qmd`` /
     ``history.qmd``;
  3. the knowledge-commit log table (``site/_history-table.md``) from the same replay frames;
  4. a staged copy of the experiment figures under ``site/experiments-figures/`` (the only path a
     Quarto *website* reliably copies into its output);
  5. the experiment report pages (``report/build_report.py`` -> ``report/experiments.qmd`` +
     ``site/experiments.qmd``);
  6. ``quarto render`` of the site into ``docs/`` (the html pages + the standalone blueprint PDF);
  7. a best-effort citable ``docs/experiments-report.pdf``; and ``docs/.nojekyll``.

The ClaimGraph library targets Python 3.13 and pulls ``ckc-lint``; run this under uv so the
dependency is provisioned without touching the system environment:

    uv run --no-project --python 3.13 \
        --with-editable /Users/aquemy/projects/hother/claimgraph python site/build.py

``--with-editable`` installs the package from its live source (a plain ``--with`` can reuse a stale
cached wheel keyed by the unchanged version); ``--no-project`` keeps uv from touching any ambient
project venv. (The ``lean-math`` plugin wraps exactly this invocation as ``bin/build-site``.)
"""
# claimgraph is provisioned at runtime by uv (see the module docstring), not installed in the
# static-analysis environment; its imports are intentionally unresolved here.
# pyright: reportMissingImports=false
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

SITE = Path(__file__).resolve().parent
REPO = SITE.parent
DOCS = REPO / "docs"
RESULTS = REPO / "experiments" / "results"
CLAIMS = REPO / "claims.toml"
FIG_STAGE = SITE / "experiments-figures"
NAME = "Measure-to-measure interpolation using Transformers"

# Pure leanblueprint/plastex leftovers in docs/ that the Quarto build does not overwrite. The
# Quarto render replaces index.html and blueprint.pdf; these have no successor and must go.
STALE_DOCS = ("dep_graph_document.html", "symbol-defs.svg", "js", "styles")


def _escape_cell(text: str) -> str:
    """Make a string safe to drop into one Markdown table cell."""
    return text.replace("|", "\\|").replace("\n", " ").strip()


def _focus_of(frame: dict[str, object]) -> str:
    """The claims a commit touched (its replay focus), as inline code, comma-separated."""
    focus = frame.get("focus")
    items = focus if isinstance(focus, (list, tuple)) else ([focus] if focus else [])
    slugs = [str(s).removeprefix("claim:") for s in items if s]
    return ", ".join(f"`{s}`" for s in slugs) if slugs else "--"


def history_table(frames: list[dict[str, object]]) -> str:
    """A Markdown table of the knowledge commits, oldest first, from the replay frames."""
    rows = ["| # | date | type | subject | touches |", "| --: | --- | --- | --- | --- |"]
    for fr in frames:
        i_val = fr.get("i", 0)
        idx = (i_val if isinstance(i_val, int) else 0) + 1
        date = str(fr.get("date", ""))[:10]
        typ = _escape_cell(str(fr.get("type", "") or ""))
        subject = _escape_cell(str(fr.get("subject", "") or ""))
        rows.append(f"| {idx} | {date} | `{typ}` | {subject} | {_focus_of(fr)} |")
    return "\n".join(rows) + "\n"


def stage_figures() -> int:
    """Copy the experiment figures into the site project so the rendered site is self-contained."""
    if FIG_STAGE.exists():
        shutil.rmtree(FIG_STAGE)
    n = 0
    for src in sorted(RESULTS.rglob("*")):
        if src.suffix.lower() in (".png", ".svg") and src.is_file():
            dest = FIG_STAGE / src.relative_to(RESULTS)
            dest.parent.mkdir(parents=True, exist_ok=True)
            _ = shutil.copy2(src, dest)
            n += 1
    return n


def clean_stale_docs() -> None:
    for name in STALE_DOCS:
        target = DOCS / name
        if target.is_dir():
            shutil.rmtree(target, ignore_errors=True)
        elif target.exists():
            target.unlink()


def run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[bytes]:
    print(f"$ {' '.join(cmd)}  (cwd={cwd.relative_to(REPO) if cwd != REPO else '.'})")
    return subprocess.run(cmd, cwd=str(cwd))


def main() -> int:
    # claimgraph is provisioned at runtime (see the module docstring); fail with an actionable
    # message if the env is not set up, rather than a bare ImportError.
    try:
        import claimgraph as cg
        from claimgraph import export_html, svg_timeline
        from claimgraph.build import read_git_dated
        from claimgraph.emit import to_dict, to_json
        from claimgraph.timeline import build_timeline
    except ModuleNotFoundError as exc:
        invocation = (
            "  uv run --no-project --python 3.13"
            " --with-editable /Users/aquemy/projects/hother/claimgraph python site/build.py"
        )
        sys.exit(f"could not import claimgraph ({exc}). Run this under uv with the package:\n{invocation}")

    DOCS.mkdir(parents=True, exist_ok=True)
    claims_path = str(CLAIMS) if CLAIMS.exists() else None

    # 1-3. ClaimGraph: end-state graph + replay frames -> json, viewer, timeline, commit log.
    print("regenerating the ClaimGraph from git history ...")
    graph = cg.build_view(str(REPO), claims=claims_path)
    registry = cg.load_registry(claims_path)
    frames = build_timeline(read_git_dated(str(REPO)), registry)

    (REPO / "claimgraph.json").write_text(to_json(graph, timeline=frames) + "\n", encoding="utf-8")
    payload = to_dict(graph, timeline=frames)
    (DOCS / "claimgraph-viewer.html").write_text(
        export_html.render(payload, shape="page", title=NAME), encoding="utf-8"
    )
    (DOCS / "history-timeline.html").write_text(
        svg_timeline.render(
            graph, frames, title=f"{NAME} -- history",
            hint="Drag the slider through the knowledge commits; each node's colour is its status as of that commit.",
        ),
        encoding="utf-8",
    )
    (SITE / "_history-table.md").write_text(history_table(frames), encoding="utf-8")
    print(f"  {len(graph.nodes)} nodes, {len(frames)} commit frames")

    # 4. Stage the experiment figures inside the site project.
    nfig = stage_figures()
    print(f"staged {nfig} experiment figures under {FIG_STAGE.relative_to(REPO)}")

    # 5. Regenerate the experiment report pages (report/experiments.qmd + site/experiments.qmd).
    print("regenerating the experiment report pages ...")
    if run([sys.executable, str(REPO / "report" / "build_report.py")], REPO).returncode != 0:
        return 1

    # 6. Render the website into docs/ (html pages + the standalone blueprint PDF).
    clean_stale_docs()
    print("rendering the Quarto site into docs/ ...")
    if run(["quarto", "render"], SITE).returncode != 0:
        return 1

    # 7a. Best-effort citable PDF report (links from the experiments page); a xelatex hiccup here
    # must not fail the site build, so this is tolerated.
    print("rendering the citable experiment report PDF (best-effort) ...")
    rep = run(["quarto", "render", "experiments.qmd", "--to", "pdf"], REPO / "report")
    pdf = REPO / "report" / "experiments.pdf"
    if rep.returncode == 0 and pdf.exists():
        shutil.copy2(pdf, DOCS / "experiments-report.pdf")
        print(f"  -> {(DOCS / 'experiments-report.pdf').relative_to(REPO)}")
    else:
        print("  warning: report PDF not produced; the website download link will 404 until built.")

    # 7b. Classic Pages: keep Jekyll from eating the underscore-prefixed Quarto assets.
    (DOCS / ".nojekyll").touch()
    print(f"\ndone. The site is in {DOCS.relative_to(REPO)}/ (open docs/index.html).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
