export const meta = {
  name: 'lean-build-leaves',
  description: 'Sequentially build, verify, land, and record a dependency-ordered set of leaf-groups from a lean-investigate plan.',
  whenToUse: 'GIT-MUTATING. Only after lean-investigate returned status:planned. Never invoke this more than once concurrently against this repo, regardless of target -- it branches, commits, pushes, and merges PRs.',
  phases: [
    { title: 'Preflight', detail: 'clean-main + concurrent-session check before touching git' },
    { title: 'Build', detail: 'sequential pipeline over groups: verify in scratch, write, build, audit, lint, commit, PR, watch, merge, rebase' },
    { title: 'Record', detail: 'append banked/blocked results to project memory' },
  ],
}

// args: { target: string, groups: Array<Group>, memoryTopic?: string }
//   groups        -- lean-investigate's plan.groups output (or a hand-edited copy/subset of it).
//                     Each group: { groupId, rationale, risk?, dependsOnGroups?, leaves: [
//                       { name, kind: 'leaf'|'foundation'|'axiom-narrowing', statementSketch, targetFile }
//                     ] }
//   memoryTopic   -- optional override for which memory file to append results to (default: target).
// Returns: { target, groupsAttempted, banked: [...], partial: [...], blocked: [...], record }

const REPO = '/Users/aquemy/projects/hother/sandbox/sandbox-proof/measure-to-measure-interpolation-using-transformers'
const MEMDIR = '/Users/aquemy/.claude/projects/-Users-aquemy-projects-hother-sandbox-sandbox-proof-measure-to-measure-interpolation-using-transformers/memory'

// This harness has been observed serializing an object `args` input to a JSON string before
// exposing it as the `args` global, despite the tool docs specifying it should arrive verbatim.
// Defensively parse either shape.
const parsedArgs = typeof args === 'string' ? JSON.parse(args) : args

if (!parsedArgs || !parsedArgs.target || !Array.isArray(parsedArgs.groups) || parsedArgs.groups.length === 0) {
  throw new Error('lean-build-leaves requires args.target and a non-empty args.groups (from lean-investigate)')
}
const target = parsedArgs.target
const groups = parsedArgs.groups
const memoryTopic = parsedArgs.memoryTopic || target

const GOTCHAS = `
Repo-specific Lean gotchas (apply as needed, do not re-derive from scratch):
- Eucl d's MetricSpace instance can time out generic unification proofs; prove such lemmas over an
  abstract [MetricSpace E] in a file with no Eucl import, then apply (not re-elaborate) them where
  Eucl d is needed (see MeasureToMeasure/Leaves/UniformRadiusPacking.lean + UniformRadiusPackingUnit.lean).
- MeasureToMeasure (bare) vs MeasureToMeasure.Foundations are two different namespaces; a wrong
  \`open\` produces cascading "Unknown identifier" errors that look like missing imports. Use
  #check @identifier in isolation to diagnose, not more imports.
- Never \`import Mathlib\` wholesale. Find the precise submodule via lean_leansearch; sanity-check
  job count with \`time lake build\` before committing an import change.
- Circular imports: extract shared vocabulary needed by both an axiom-statement file and a leaf
  file into its own low-level file both import directly.
- lean_run_code's sandbox can occasionally report a spurious error unrelated to a real file's
  correctness -- trust \`lake build\` on the real file over an isolated scratch discrepancy once
  both pieces have been tested in isolation.
- A kernel-clean theorem can still have an unsatisfiable/vacuous hypothesis -- sanity-check
  satisfiability before calling a leaf done.
- Never delete a hypothesis the paper's scope needs just because the current proof doesn't use it;
  keep it prefixed _ instead (this codebase's convention).
`

const CKC_CONVENTION = `
CKC commit convention (CONTRIBUTING.md, verbatim -- follow exactly, this is enforced by a commit-msg
hook via pre-commit + ckc-tools v0.3.0):

Grammar: <type>[~][(scope)][!]: <description>, then a body paragraph, then footers (git trailers).
House style: plain, non-LLM voice. NO EM DASHES anywhere in the commit message (title, body, or
footers) -- use a comma, colon, or a new sentence instead. This is a hard repo style rule.

STATUS RULE (hard, no exceptions -- this is the repo's kernel-honesty invariant, and past runs got
it wrong by pattern-matching the examples below): the Status footer is determined ONLY by step 7's
lean_verify output for the leaf's FQN.
- Axiom list is EXACTLY [propext, Classical.choice, Quot.sound] -> Status: math.machine-checked,
  plain type (\`formalize(scope):\`).
- Axiom list contains ANY project axiom (lemma_3_3, prop_2_2, exists_parked_schedule, ...) ->
  Status: math.axiomatised, tilde type (\`formalize~(scope):\` or \`proof~(scope):\`), and the Axioms
  footer MUST list the real closure verbatim including the project axioms. Never write
  math.machine-checked on a commit whose own Axioms footer lists a project axiom.
- The Status footer is NEVER omitted, on any commit type.

Pick type per situation:
- Landing a genuinely NEW kernel-clean lemma: \`formalize(scope): <what was proved>\`
  Status: math.machine-checked
  Lean: <FQN>
  Axioms: '<FQN>' depends on axioms: [propext, Classical.choice, Quot.sound]
  Closes: claim:<slug>          (only if this discharges a registered claims.toml slug)
  Depends-On: <FQN or claim:slug>  (repeat as needed)
- Landing a new lemma whose closure includes a PROJECT axiom (per the STATUS RULE above):
  \`formalize~(scope): <what was proved, conditionally>\`
  Status: math.axiomatised
  Lean: <FQN>
  Axioms: '<FQN>' depends on axioms: [propext, Classical.choice, Quot.sound, MeasureToMeasure.Statements.lemma_3_3]
  Depends-On: <the axiom's FQN>
- Discharging an EXISTING axiom into a real theorem (an axiom becomes proved): \`proof(scope): <what was discharged>\`
  Status: math.machine-checked
  Lean: <FQN>
  Axioms: '<FQN>' depends on axioms: [propext, Classical.choice, Quot.sound]
  Closes: <the axiom's FQN or claim:slug>
- Extending an existing theorem's conclusion without changing its proof obligation shape: \`strengthen(scope): <what got stronger>\`
- Dropping an unneeded hypothesis or widening a class the theorem already covers: \`generalize(scope): <what got more general>\`
- Admitting a NEW or NARROWED axiom (kind:'axiom-narrowing' leaves only -- full protocol below):
  \`axiomatize~(scope): <the axiom, one line>\`
  Status: math.axiomatised
  AXIOM: <name> (<why Lean/Mathlib can't yet prove it>)
  Lean: <FQN>
  Source-Ref: <work, statement, page>
  Refutation-Attempt: <artifact path, or "scratch attack found no refutation">
  Closes: claim:<slug>   (if applicable)

Every commit ends with the FULL Claude-Session trailer, never truncated or paraphrased:
Claude-Session: <the complete https://claude.ai/code/session_... URL given in your system prompt>
(Copy it verbatim from the system prompt's git guidance. A truncated or missing trailer is a
footer-drift erratum; past run #287 shipped one.)
Never use \`--amend\` after a hook failure on a fresh commit -- fix the issue, re-stage, commit fresh.

Two worked examples (CONTRIBUTING.md, verbatim):

formalize(leaves): prove the tangential projector inner-product identity

Lean: MeasureToMeasure.Leaves.projector_inner_sub_sq
Status: math.machine-checked
Axioms: 'projector_inner_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
Closes: claim:leaf-projector
Depends-On: MeasureToMeasure.Foundations.tangentialProjector

---

axiomatize~(wasserstein): assume W2 with Kantorovich-Rubinstein duality

CKC honest record: Mathlib lacks a developed optimal-transport / Wasserstein theory, so W2 and
its duality are introduced as axioms here. Fidelity diff and degenerate attack per the axiom
admission protocol (WORKFLOW.md); no refutation found.
Lean: MeasureToMeasure.Axioms.W2
Status: math.axiomatised
AXIOM: W2 (no Mathlib optimal-transport theory at v4.31.0)
Source-Ref: Villani 2009, Thm 5.10 (Kantorovich duality), p.57
Refutation-Attempt: Regression/NonVacuity/Wasserstein.lean (witness; attack found no refutation)
Closes: claim:lem-5-2
`

const AXIOM_PROTOCOL = `
Full WORKFLOW.md axiom admission protocol (required for every kind:'axiom-narrowing' leaf, verbatim):
1. Verbatim anchor: the axiom's docstring quotes the source statement verbatim with a page anchor
   (e.g. "Lemma 3.2, p.15, arXiv:2411.04551v3").
2. Six-axis fidelity diff in the commit body: objects (measure class), hypotheses (each source
   hypothesis present/strengthened/dropped-with-justification), quantifier order (family vs single
   object), conclusion strength, quantitative content (never invent constants), model class.
3. Degenerate-instantiation attack in a SCRATCH file BEFORE admission: equal measures (mu := nu),
   zero measure, infinite measure (volume), off-sphere points, boundary d in {0,1,2}. A compiling
   proof of False means the statement is wrong: fix it, then commit the disproof and a must-fail
   adapter per the regression suite below.
4. Non-vacuity witness in Regression/NonVacuity/: concrete data satisfying every hypothesis, applied
   to the axiom as a FULL application with an explicit conclusion-type ascription
   (\`have _h : <the axiom's conclusion for this witness> := <axiom> <all args>\` inside an example,
   or \`example : <conclusion> := ...\`). A bare partial application is FORBIDDEN: it typechecks even
   when later-added hypotheses are unsatisfiable, so it silently stops guarding (this exact hole hid
   the hgenRest vacuity for 8 days, finding F22). If a later PR ADDS hypotheses to a guarded
   statement, that PR must extend the witness to cover the whole new bundle or, if it cannot, say so
   in the commit body and downgrade the claim's status.
5. Model adequacy: one paragraph in the commit on whether the formal class the axiom quantifies over
   can express what the source's PROOF actually uses.
6. Footers: Source-Ref: <work, statement, page> and Refutation-Attempt: <artifact path>.

Refutation regression suite (only if the admission audit kernel-refuted a looser draft along the
way): transcribe the refuted signature as an abbrev ...Sig in Regression/OldStatements.lean, commit
the disproof as theorem ..._false : ...Sig -> False in Regression/Refuted/, and add a short
must-fail adapter example : ...Sig := fun ... => current_axiom ... in
Refutations/F<nn>_<axiom>_<exploit>.lean (pick the next free F<nn> by checking existing files in
Refutations/). scripts/audit.sh's refutation-gate step will assert it still fails for the right
reason.
`

const CYCLE = `
Per-leaf build cycle. Treat every numbered step as a hard gate: never proceed past a red one, and
never write a \`sorry\` anywhere (it fails scripts/audit.sh).

CRITICAL runtime constraint: this agent runs inside a workflow whose harness kills and retries the
whole agent if it sees no new tool call for about 180 seconds. \`lake build\`, \`bash scripts/audit.sh\`,
\`lake lint\`, and \`gh pr checks --watch\` on this project routinely run well past that (a cold full
build alone is 10+ minutes) with NO intermediate output, which trips the stall detector and wastes
the entire attempt. NEVER run any of those four commands as a single blocking foreground Bash call.
Instead, for each one: launch it with the Bash tool's \`run_in_background: true\`, then poll its
status periodically (a short \`sleep\` + status check loop, or repeated small tool calls a comfortably
under 180s apart) until it finishes, then read its output. This keeps the agent visibly making tool
calls throughout instead of going silent for the whole run.

1. Verify the core idea in mcp__plugin_lean-math_lean-lsp__lean_run_code SCRATCH first (evidence
   only, not proof of real-file correctness -- the sandbox can occasionally report a spurious error
   unrelated to real-file correctness).
2. Write the real file. If it's a new file, add its import to the root MeasureToMeasure.lean
   aggregator, in a sensible position near related imports.
3. Confirm with lean_diagnostic_messages on the real file, or a targeted \`lake build <target>\`
   (background + poll per the runtime constraint above if it's not near-instant).
4. Full \`lake build\` from repo root at ${REPO}. Zero errors. Background + poll (see above).
5. \`bash scripts/audit.sh\` from repo root. Must end with the literal line \`audit: PASS\`.
   Background + poll (see above).
6. \`lake lint\` (bare, no target) from repo root, run EXPLICITLY and SEPARATELY -- it is not covered
   by audit.sh and has silently broken CI before while everything else passed locally. Must be clean
   (watch especially for unusedArguments on any new/changed declaration). Background + poll.
7. lean_verify on the new declaration's FQN. Axiom list must be exactly propext, Classical.choice,
   Quot.sound, plus only a deliberate new hypothesis you intended to add.
8. Sanity-check the new hypothesis is actually satisfiable: point to (or write) a concrete
   instantiation, don't just assume. If the leaf GUARDS a public statement (its hypotheses gate a
   theorem others will invoke), the instantiation must be a FULL application with an explicit
   conclusion-type ascription (see the witness rule in the axiom protocol below); a partial
   application is not a satisfiability check.
9. If kind is 'axiom-narrowing': run the FULL axiom admission protocol below before committing.
${AXIOM_PROTOCOL}
9b. Ledger duty: if this leaf produced a FINDING-grade fact (a kernel refutation, a paper erratum,
    an admitted axiom, a discovered gap in the paper's own construction, a vacuity), append the
    corresponding RESEARCH.md finding entry (next free F<nn>) and, for errata, the ERRATA.md entry
    (next free E<n>) IN THE SAME PR as the Lean change. The ledger is a status surface; it must not
    trail the code (it once went 84 PRs stale).
10. Resume-safety: before \`git checkout -b\`, check \`git branch -a\` and \`gh pr list\` for a branch
    or PR already matching this leaf (a prior crashed run) -- resume it instead of duplicating.
11. Branch off a freshly-rebased main (\`git fetch origin && git rebase origin/main\` first).
    \`git add\` the SPECIFIC files touched (never -A / .). Commit using the CKC convention below.
${CKC_CONVENTION}
12. \`git push -u origin <branch>\`, \`gh pr create\` with a body that includes a Test-plan checklist
    covering steps 4-7 (build, audit, lint, axiom-check). For CI: do NOT run \`gh pr checks --watch\`
    as a single blocking call (CI on this repo routinely takes several minutes with no output, which
    trips the same stall detector) -- instead background it or poll \`gh pr checks <N>\` periodically
    until it reports a final state, then \`gh pr merge <N> --squash --delete-branch\` immediately on
    green (this repo's current convention,
    confirmed against PRs #262-266 -- squash-merge, not a merge commit), then
    \`git checkout main && git fetch origin && git rebase origin/main\` before the next leaf.

If a leaf hits a genuine wall (the construction doesn't close, or would require unsound reasoning):
STOP that leaf, do not force a sorry or an unsound proof, report it blocked with a precise reason
including what was tried, and mark any leaf in this or a later group that depends on it as
blocked-by-dependency. Do not abort the whole run over one blocked leaf.
`

phase('Preflight')

const PREFLIGHT_SCHEMA = {
  type: 'object',
  properties: {
    go: { type: 'boolean' },
    reason: { type: 'string' },
  },
  required: ['go', 'reason'],
}

const preflight = await agent(
  `Repo: ${REPO}\n\n` +
  `Before any git-mutating work on target "${target}": check \`gh pr list --state open\` and ` +
  `\`git branch --show-current\` / \`git status\` for signs a concurrent session is already working ` +
  `this exact target or campaign (per this repo's own memory notes on concurrent sessions sharing ` +
  `this git tree -- grep ${MEMDIR}/no-concurrent-mutating-forks.md and ` +
  `${MEMDIR}/concurrent-session-shared-state.md for the detection pattern). If clear: ` +
  `\`git checkout main && git fetch origin && git rebase origin/main\`, then confirm \`lake build\` ` +
  `is currently green from a clean main. Report go:true only if both checks pass; go:false with a ` +
  `precise reason otherwise (a concurrent session's branch/PR name, or the build failure).`,
  { label: 'preflight', phase: 'Preflight', schema: PREFLIGHT_SCHEMA }
)

if (!preflight || !preflight.go) {
  return { status: 'blocked-preflight', target, reason: preflight ? preflight.reason : 'preflight agent returned no result' }
}

phase('Build')

const GROUP_SCHEMA = {
  type: 'object',
  properties: {
    groupId: { type: 'string' },
    leafResults: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          name: { type: 'string' },
          status: { type: 'string', enum: ['merged', 'partial', 'blocked', 'blocked-by-dependency'] },
          prNumber: { type: 'number' },
          fqn: { type: 'string' },
          reason: { type: 'string' },
        },
        required: ['name', 'status'],
      },
    },
    summary: { type: 'string' },
  },
  required: ['groupId', 'leafResults', 'summary'],
}

const bankedSoFar = []
const blockedGroupIds = new Set()

// STRICTLY SEQUENTIAL over groups: every build agent mutates the ONE shared working tree and git
// HEAD (branch, commit, rebase), so two groups building at once collide (the repo's own
// no-concurrent-mutating-forks memory). A pipeline() here let dependency-free groups run
// concurrently; in the 2026-07-27 run one agent had to bypass the local commit hook via git
// plumbing to dodge a sibling's checkout. Sequential also makes bankedSoFar genuinely cumulative.
const buildResults = []
for (const group of groups) {
  const blockedDep = (group.dependsOnGroups || []).find((g) => blockedGroupIds.has(g))
  if (blockedDep) {
    buildResults.push({
      groupId: group.groupId,
      leafResults: group.leaves.map((l) => ({ name: l.name, status: 'blocked-by-dependency', reason: `depends on blocked group ${blockedDep}` })),
      summary: `skipped: depends on blocked group ${blockedDep}`,
    })
    continue
  }
  const result = await agent(
    `Repo: ${REPO}\nTarget campaign: "${target}"\nGroup: ${group.groupId} -- ${group.rationale}\n` +
    `Risk noted: ${group.risk || '(none noted)'}\n` +
    `Leaves in this group (build them in order, each through the full cycle before starting the next):\n` +
    `${JSON.stringify(group.leaves, null, 2)}\n\n` +
    `Already banked earlier in this run (for context/reuse, do not re-derive): ${JSON.stringify(bankedSoFar)}\n\n` +
    `${CYCLE}\n${GOTCHAS}\n\n` +
    `Report one entry per leaf in this group with its final status. A 'partial' status means real ` +
    `progress was made (e.g. a supporting lemma landed) but the named leaf itself did not fully ` +
    `land -- explain what's missing in 'reason'.`,
    // effort 'high', not 'xhigh': an earlier xhigh-effort run on this repo went silent for
    // 30+ minutes between tool calls (likely long per-turn generation latency compounding with
    // a large cached prompt), tripping the workflow harness's ~180s no-progress stall detector
    // on every retry. Build work here is mostly mechanical (follow CYCLE, run gated tools) --
    // it does not need xhigh's extra deliberation the way Investigate's synthesis does.
    { label: `build:${group.groupId}`, phase: 'Build', schema: GROUP_SCHEMA, effort: 'high' }
  )
  if (!result) {
    blockedGroupIds.add(group.groupId)
    log(`group ${group.groupId}: agent returned no result, treating as blocked`)
    buildResults.push({ groupId: group.groupId, leafResults: group.leaves.map((l) => ({ name: l.name, status: 'blocked', reason: 'build agent returned no result' })), summary: 'no result' })
    continue
  }
  const anyBlocked = result.leafResults.some((r) => r.status === 'blocked' || r.status === 'blocked-by-dependency')
  if (anyBlocked) blockedGroupIds.add(group.groupId)
  const merged = result.leafResults.filter((r) => r.status === 'merged').map((r) => r.name)
  bankedSoFar.push(...merged)
  log(`group ${group.groupId}: ${result.summary}`)
  buildResults.push(result)
}

phase('Record')

const flat = buildResults.filter(Boolean).flatMap((r) => r.leafResults.map((l) => ({ ...l, groupId: r.groupId })))
const banked = flat.filter((l) => l.status === 'merged')
const partial = flat.filter((l) => l.status === 'partial')
const blocked = flat.filter((l) => l.status === 'blocked' || l.status === 'blocked-by-dependency')

const RECORD_SCHEMA = {
  type: 'object',
  properties: {
    memoryFile: { type: 'string' },
    appended: { type: 'boolean' },
    summary: { type: 'string' },
  },
  required: ['appended', 'summary'],
}

const record = await agent(
  `Memory dir: ${MEMDIR}\n\n` +
  `lean-build-leaves finished a run for target "${target}" (memory topic: "${memoryTopic}").\n` +
  `Banked: ${JSON.stringify(banked)}\nPartial: ${JSON.stringify(partial)}\nBlocked: ${JSON.stringify(blocked)}\n\n` +
  `Find the topic memory file (grep ${MEMDIR}/*.md for "${memoryTopic}" or a close relative -- an ` +
  `existing "<topic>-campaign.md" is likely). If one exists, APPEND a new dated section (get the ` +
  `date via Bash \`date +%Y-%m-%d\`) with these results and any notable gotchas hit, matching the ` +
  `file's existing frontmatter/style exactly -- never overwrite prior content, and be exactly as ` +
  `honest about partial/blocked leaves as about merged ones. If none exists, create one following ` +
  `the frontmatter convention used by other files in that directory (name, description, ` +
  `metadata.type: project). Then update ${MEMDIR}/MEMORY.md's index: add or refresh the one-line ` +
  `pointer for this file, leaving every other line unchanged, keeping entries under ~150 chars and ` +
  `the file under its existing 200-line limit.`,
  { label: 'record', phase: 'Record', schema: RECORD_SCHEMA }
)

return { target, groupsAttempted: groups.length, banked, partial, blocked, record }
