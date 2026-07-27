export const meta = {
  name: 'lean-investigate',
  description: 'Scope a target axiom/gap in MeasureToMeasure: paper-fidelity + existing-infra research, synthesized into a dependency-ordered leaf-group build plan, or an honest blocked verdict. Read-only.',
  whenToUse: 'Before starting any new de-axiomatization campaign on this repo, or before resuming a paused one. Safe to run repeatedly and concurrently across different targets -- it never touches git.',
  phases: [
    { title: 'Investigate', detail: 'parallel: paper-fidelity scoping (image PDF) + existing-infra/memory search' },
    { title: 'Probe', detail: 'conditional: a degenerate-instantiation counterexample attempt, only if fidelity found a suspected gap' },
    { title: 'Plan', detail: 'synthesize into a dependency-ordered leaf-group plan, or a precise blocked verdict' },
    { title: 'Record', detail: 'only on blocked: append an honest negative-result memory entry' },
  ],
}

// args: { target: string, scopeHint?: string }
//   target    -- an axiom/lemma name (e.g. "exists_disentangling_balls") or a precise gap
//                description if there is no single named axiom yet.
//   scopeHint -- optional freeform steer (e.g. "leaf 4 only", "just the induction skeleton").
// Returns either:
//   { status: 'planned', target, plan }   -- plan.groups is the input lean-build-leaves expects
//   { status: 'blocked', target, plan, recorded }

const REPO = '/Users/aquemy/projects/hother/sandbox/sandbox-proof/measure-to-measure-interpolation-using-transformers'
const MEMDIR = '/Users/aquemy/.claude/projects/-Users-aquemy-projects-hother-sandbox-sandbox-proof-measure-to-measure-interpolation-using-transformers/memory'

// This harness has been observed serializing an object `args` input to a JSON string before
// exposing it as the `args` global, despite the tool docs specifying it should arrive verbatim.
// Defensively parse either shape.
const parsedArgs = typeof args === 'string' ? JSON.parse(args) : args

if (!parsedArgs || !parsedArgs.target) {
  throw new Error('lean-investigate requires args.target (an axiom/lemma name or gap description)')
}
const target = parsedArgs.target
const scopeHint = parsedArgs.scopeHint || ''

const GOTCHAS = `
Repo-specific Lean gotchas to watch for while researching (do not re-derive these from scratch,
they are already known; cite them if they apply to this target):

- Eucl d := EuclideanSpace ℝ (Fin d)'s MetricSpace instance (via PiLp) is definitionally heavy
  enough that Finset.inf'-style implicit-argument unification can time out with Eucl d in scope,
  though the identical proof is instant over an abstract [MetricSpace E]. Pattern: prove generic
  geometric/combinatorial lemmas in a file with NO Eucl-touching import, then apply (never
  re-elaborate) the theorem in a separate Eucl-specific file (see
  MeasureToMeasure/Leaves/UniformRadiusPacking.lean + UniformRadiusPackingUnit.lean).
- Two different namespaces: Eucl, sphere, Params, measureFlow live in the bare MeasureToMeasure
  namespace (Foundations/Sphere.lean, FlowMap.lean); AttnParams, attnStep, IsMeanFieldFlow live in
  MeasureToMeasure.Foundations (Foundations/Attention.lean). A wrong 'open' produces a cascade of
  "Unknown identifier / Function expected" errors that look exactly like missing imports. Diagnose
  with #check @identifier in isolation, not by guessing more imports.
- Never 'import Mathlib' (the whole library) as a quick fix for a missing identifier -- it can
  balloon a targeted lake build job count several-fold for one file. Find the precise submodule via
  lean_leansearch on the bare identifier name, and sanity-check job count with 'time lake build'.
- Circular imports: a new file needing both axiom-statement-level vocabulary and leaf-level
  machinery can cycle if the axiom-statement file later imports the leaf. Fix: extract the shared
  vocabulary into its own low-level file both sides import directly (see Statements/SupportedIn.lean).
- A kernel-clean (sorry-free) theorem can still have an unsatisfiable/vacuous hypothesis -- always
  confirm a new lemma's hypotheses are actually satisfiable in the intended application before
  treating a leaf as usable.
- When the paper's own construction has a genuine gap, state a corrected, narrower hypothesis
  (documented precisely per the WORKFLOW.md axiom admission protocol below) -- never force an
  unsound proof of the original over-general statement.
- Never drop a hypothesis just because the current proof route does not need it, if it is faithful
  to the paper's scope -- keep it prefixed \`_\` (this codebase's convention for "present but
  currently unused").
`

const AXIOM_PROTOCOL = `
This repo's WORKFLOW.md axiom admission protocol (verbatim summary -- an axiom is ADMITTED, not
merely written): before any new \`axiom\` lands in Statements/ or Axioms/, it needs (1) a verbatim
source-anchored docstring quote with a page anchor, (2) a six-axis fidelity diff (objects,
hypotheses present/strengthened/dropped-with-justification, quantifier order, conclusion strength,
quantitative content -- never invent constants, model class), (3) a degenerate-instantiation attack
attempted in scratch BEFORE admission (equal measures, zero/infinite measure, off-sphere points,
boundary d in {0,1,2}) -- a compiling False means the statement is wrong and must be fixed, (4) a
non-vacuity witness for Regression/NonVacuity/, (5) a model-adequacy paragraph (can the formal class
express what the source's PROOF actually uses?), (6) Source-Ref: and Refutation-Attempt: commit
footers. If a target looks like it needs a genuinely new or narrowed axiom, flag that explicitly in
the plan as an 'axiom-narrowing' leaf so lean-build-leaves runs the full protocol.
`

phase('Investigate')

const PAPER_SCHEMA = {
  type: 'object',
  properties: {
    paperRefs: { type: 'array', items: { type: 'string' } },
    objects: { type: 'string', description: 'measure class involved: probability? sphere-supported? etc' },
    hypotheses: { type: 'array', items: { type: 'string' } },
    quantifierOrder: { type: 'string' },
    conclusionStrength: { type: 'string' },
    statementSketch: { type: 'string', description: 'a proposed Lean statement sketch for the target' },
    suspectedGap: { type: 'boolean', description: 'true if the paper\'s own construction looks incomplete or hand-waved for this target' },
    suspectedGapDetail: { type: 'string' },
    summary: { type: 'string' },
  },
  required: ['statementSketch', 'suspectedGap', 'summary'],
}

const INFRA_SCHEMA = {
  type: 'object',
  properties: {
    reusableLeaves: { type: 'array', items: { type: 'string' }, description: 'existing FQNs/files that look directly reusable' },
    priorAttempts: { type: 'string', description: 'anything memory/RESEARCH.md records about prior work on this exact target, including negative findings' },
    gaps: { type: 'array', items: { type: 'string' }, description: 'infra that does not yet exist and would need to be built' },
    summary: { type: 'string' },
  },
  required: ['summary'],
}

const [paperFindings, infraFindings] = await parallel([
  () => agent(
    `Repo: ${REPO}\n\n` +
    `Read ${REPO}/references/paper.pdf as IMAGES (this is Geshkovski-Rigollet-Ruiz-Balet, ` +
    `"Measure-to-measure interpolation using Transformers", arXiv:2411.04551). Find the exact ` +
    `source statement corresponding to this target: "${target}". Scope hint: "${scopeHint}".\n\n` +
    `Cross-check against the current Lean text in the repo (grep MeasureToMeasure/Statements, ` +
    `MeasureToMeasure/Axioms for the target name or related lemma numbers) to see what is already ` +
    `stated in Lean and how it compares to the paper.\n\n` +
    `Report: the paper's objects/hypotheses/quantifier-order/conclusion for this statement, a ` +
    `proposed Lean statement sketch, and whether the paper's OWN construction/proof looks complete ` +
    `for this statement or has a suspected gap (with a precise page anchor if so -- do not hand-wave ` +
    `this call either way).\n\n${AXIOM_PROTOCOL}`,
    { label: 'paper-fidelity', phase: 'Investigate', schema: PAPER_SCHEMA, effort: 'xhigh' }
  ),
  () => agent(
    `Repo: ${REPO}\nMemory dir: ${MEMDIR}\n\n` +
    `Target: "${target}". Scope hint: "${scopeHint}".\n\n` +
    `Grep MeasureToMeasure/Leaves, MeasureToMeasure/Foundations, MeasureToMeasure/Statements, ` +
    `MeasureToMeasure/Axioms, and ${REPO}/RESEARCH.md for anything already built that is reusable ` +
    `toward this target (existing leaves, foundation lemmas, related axioms). Separately grep ` +
    `${MEMDIR}/*.md and ${MEMDIR}/MEMORY.md for prior investigation of this EXACT target -- surface ` +
    `honest negative findings (things already tried and found blocked) so they are not silently ` +
    `re-attempted. If a campaign memory file already exists for this target, read it in full and ` +
    `summarize its current state precisely (what's banked, what's blocked, what's untouched).\n\n${GOTCHAS}`,
    { label: 'existing-infra', phase: 'Investigate', schema: INFRA_SCHEMA, effort: 'high' }
  ),
])

phase('Probe')

let probeFindings = null
if (paperFindings && paperFindings.suspectedGap) {
  const PROBE_SCHEMA = {
    type: 'object',
    properties: {
      attempted: { type: 'boolean' },
      refuted: { type: 'boolean', description: 'true if a degenerate instantiation produced a compiling proof of False' },
      evidence: { type: 'string', description: 'the lean_run_code snippet and its result' },
      summary: { type: 'string' },
    },
    required: ['attempted', 'refuted', 'summary'],
  }
  probeFindings = await agent(
    `Repo: ${REPO}\n\n` +
    `The paper-fidelity research found a suspected gap for target "${target}":\n` +
    `${paperFindings.suspectedGapDetail || '(no detail given)'}\n\n` +
    `Statement sketch under scrutiny:\n${paperFindings.statementSketch}\n\n` +
    `Attempt the WORKFLOW.md step-3 degenerate-instantiation attack in lean_run_code SCRATCH ONLY ` +
    `(do not touch real files): try to instantiate the sketch at inputs the hypotheses should ` +
    `exclude -- equal measures (mu := nu), the zero measure, an infinite measure (volume), ` +
    `off-sphere points, boundary dimensions d in {0,1,2}. Report whether any instantiation yields a ` +
    `compiling proof of False (a real refutation) or whether the statement survives all attempts.`,
    { label: 'degenerate-probe', phase: 'Probe', schema: PROBE_SCHEMA, effort: 'high' }
  )
}

phase('Plan')

const PLAN_SCHEMA = {
  type: 'object',
  properties: {
    status: { type: 'string', enum: ['planned', 'blocked'] },
    axiomFqn: { type: 'string' },
    paperRefs: { type: 'array', items: { type: 'string' } },
    groups: {
      type: 'array',
      description: 'dependency-ordered build groups, 1-3 tightly-coupled leaves each; independent leaves get their own group',
      items: {
        type: 'object',
        properties: {
          groupId: { type: 'string' },
          rationale: { type: 'string' },
          risk: { type: 'string' },
          dependsOnGroups: { type: 'array', items: { type: 'string' } },
          leaves: {
            type: 'array',
            items: {
              type: 'object',
              properties: {
                name: { type: 'string' },
                kind: { type: 'string', enum: ['leaf', 'foundation', 'axiom-narrowing'] },
                statementSketch: { type: 'string' },
                targetFile: { type: 'string' },
              },
              required: ['name', 'kind', 'statementSketch', 'targetFile'],
            },
          },
        },
        required: ['groupId', 'rationale', 'leaves'],
      },
    },
    blockedReason: { type: 'string' },
    evidence: { type: 'string' },
    summary: { type: 'string' },
  },
  required: ['status', 'summary'],
}

const plan = await agent(
  `Synthesize a build plan for target "${target}" (scope hint: "${scopeHint}") from these two ` +
  `research reports and the probe (if any). Do NOT force a fake plan -- if the evidence points to a ` +
  `genuine wall (the paper's own construction has an unclosable gap, required infra does not exist ` +
  `and would be a multi-week undertaking, or a prior attempt in memory already found this blocked ` +
  `for a reason that still holds), return status:'blocked' with precise evidence instead.\n\n` +
  `Paper-fidelity report:\n${JSON.stringify(paperFindings)}\n\n` +
  `Existing-infra report:\n${JSON.stringify(infraFindings)}\n\n` +
  `Degenerate-probe report:\n${JSON.stringify(probeFindings)}\n\n` +
  `If planned: break the work into small dependency-ordered groups (1-3 tightly-coupled leaves per ` +
  `group; independent leaves get their own group so lean-build-leaves can report partial progress ` +
  `precisely). Each leaf needs a name, a kind (leaf / foundation / axiom-narrowing), a statement ` +
  `sketch, and a target file path (reuse an existing file where it fits the codebase's existing ` +
  `per-topic file layout under MeasureToMeasure/Leaves, .../Foundations, or .../Statements). Mark ` +
  `any leaf that introduces or narrows an axiom as kind:'axiom-narrowing' explicitly -- that flag is ` +
  `what tells lean-build-leaves to run the full WORKFLOW.md protocol on it.\n\n${AXIOM_PROTOCOL}${GOTCHAS}`,
  { label: 'synthesize-plan', phase: 'Plan', schema: PLAN_SCHEMA, effort: 'xhigh' }
)

if (plan && plan.status === 'blocked') {
  phase('Record')
  const RECORD_SCHEMA = {
    type: 'object',
    properties: {
      memoryFile: { type: 'string' },
      appended: { type: 'boolean' },
      summary: { type: 'string' },
    },
    required: ['appended', 'summary'],
  }
  const recorded = await agent(
    `Memory dir: ${MEMDIR}\n\n` +
    `lean-investigate found target "${target}" BLOCKED. Reason: ${plan.blockedReason || '(none given)'}\n` +
    `Evidence: ${plan.evidence || '(none given)'}\nSummary: ${plan.summary}\n\n` +
    `Find the topic memory file for this target by grepping ${MEMDIR}/*.md for its name (or a close ` +
    `relative -- e.g. an existing "<target>-campaign.md"). If one exists, APPEND a new dated section ` +
    `(get the date via Bash \`date +%Y-%m-%d\`) recording this negative finding, matching the file's ` +
    `existing frontmatter/style exactly -- do not overwrite prior content. If none exists, create one ` +
    `following the frontmatter convention used by the other files in that directory (name, ` +
    `description, metadata.type: project). Then update ${MEMDIR}/MEMORY.md's index: add or update the ` +
    `one-line pointer entry for this file, keeping every other line unchanged, entries under ~150 ` +
    `chars, and the file under the existing 200-line index limit.`,
    { label: 'record-blocked', phase: 'Record', schema: RECORD_SCHEMA }
  )
  return { status: 'blocked', target, plan, recorded }
}

return { status: 'planned', target, plan }
