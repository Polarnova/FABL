# FABL contributor contract

## Mission and sources of truth

FABL formalizes the May 2021 arXiv edition of Ryan O'Donnell's *Analysis of Boolean Functions* in
Lean 4 and Mathlib. Chapters 1--3 are proof-complete; the project objective is complete coverage of
every chapter.

1. The book determines mathematical scope and complete human-readable statements.
2. Production declarations under `FABL/**/*.lean` determine formal statements and proofs.
3. Verso sources under `blueprint-verso/FABLBlueprint/**/*.lean` transcribe the book statements,
   associate them with compiled declarations, and record the reviewed mathematical dependency DAG.

The local book PDF is a normative reference but is never committed. Production Lean and Verso Lean
sources are maintained; generated HTML, PDF, manifests, graphs, summaries, statuses, and caches are
not. Do not create a parallel YAML ledger, TeX Blueprint, prose proof corpus, or handwritten status
file.

Never silently weaken a book statement, add an assumption, or replace its domain. Record any
deliberate generalization or representation bridge in the corresponding Verso node and, when it is
part of the public formal API, in the production declaration's docstring.

## Architecture

- Keep physical modules and statement coverage aligned with the book's chapters and sections.
- Let the Blueprint DAG determine proof order. Book order and proof order are deliberately distinct.
- Give a theorem's canonical public declaration to the earliest chapter in which the book formally
  states it, even when its proof is deferred. A later proof chapter must reuse that declaration, not
  create a second API. Keep proof-only helpers adjacent until real cross-chapter reuse justifies a
  narrow extraction.
- Do not introduce one global Boolean-cube representation. Use the domain stated by each theorem and
  add an explicit bridge only when a production theorem crosses representations.
- Keep mathematical definitions and proofs pure. Extraction, rendering, validation, PDF generation,
  and CI belong at the repository edge.
- Match algorithmic statements to the computation model used by the book. For Chapter 3, use a
  finite randomized random-example/membership-query program with constructor-derived oracle counts,
  explicit local-work charges, `PMF` semantics, and finite hypothesis output. Do not translate an
  oracle theorem into an ordinary Turing-machine theorem.
- Add an external complexity dependency only when an in-scope statement genuinely requires a
  machine model, complexity class, or reduction framework. At that boundary, audit the pinned
  Mathlib first, then a toolchain-matched CSLib release and specialized complexity libraries. The
  absence of such a dependency in Chapter 3 is deliberate.
- Do not add `Core`, `Common`, `Utils`, or `ToMathlib` dumping grounds. Extract a shared declaration
  only when a real downstream theorem needs it; prefer the narrowest mathematically meaningful home.
- `lean-booleanfun` is cited prior art and a search aid, not an upstream dependency. Do not import,
  vendor, or copy it. Validate every reuse idea against Mathlib and FABL.

### Module-size discipline

- Keep proof-bearing modules comparable to ordinary Mathlib and CSLib source files. Aim for
  150--900 lines of substantive Lean; review every file above 900 lines and split it before it
  exceeds 1200 lines unless a documented mathematical reason makes the split worse.
- Split only at a real mathematical or API boundary. Do not create arbitrary numbered fragments,
  and do not move declarations merely to satisfy a line count.
- Preserve the book-section module as a stable public-import aggregate when its implementation is
  divided into submodules. Downstream code and Blueprint associations must continue to use canonical
  declaration names, never duplicate restatements.
- A small aggregate, bridge, or root-import file is legitimate. The lower target applies to
  substantive proof modules, not to deliberately thin composition points.

## Existing-theorem reuse gate

Before introducing a declaration or reproving a property:

1. Search existing FABL declarations with `#check` and `rg`, especially earlier sections and
   chapters in the dependency path.
2. Search the imported environment with `#check`, `#find`, `exact?`, `apply?`, and `rw?`.
3. Search `.lake/packages/mathlib/Mathlib` with `rg` for an exact or more general theorem.
4. Reuse the established FABL theorem when it is the project's canonical book-facing API; reuse the
   underlying Mathlib theorem directly for general infrastructure.
5. Specialize a more general result or add a thin pure representation bridge before implementing a
   new theorem.
6. Implement locally only after the search establishes a genuine gap. For a genuinely new book
   theorem, follow the book's original proof and expose reusable intermediate lemmas only when the
   formal proof actually needs them.

Book-facing restatements of stronger Mathlib or earlier FABL theorems are permitted for coverage,
but their proofs must delegate to those existing results. Do not copy an earlier proof under a new
name.

## Chapter construction workflow

### 1. Extract the complete statement inventory

Before proving the chapter, read the whole in-scope section range and enter every definition, fact,
proposition, theorem, named test or algorithm, and every exercise or support lemma used by a main
proof into the matching Verso section. Each node must contain the full book-facing statement:
hypotheses, quantifiers, domains, conclusions, and displayed formulas—not merely a title or equation.

Do not expand scope opportunistically while proving. Finish and audit the chapter inventory first;
record later-book dependencies as explicit nodes rather than hiding them as assumptions.

### 2. Audit reuse and formalize signatures

For every inventory item, classify the implementation as direct Mathlib reuse, reuse of an earlier
FABL result, specialization, a thin representation bridge, or a genuine local theorem. Write the
Lean signature without changing the mathematics, choose Mathlib-style names, and attach the Verso
node to the actual declarations with `lean :=`.

A temporary `sorry` is allowed only in an explicitly active WIP working tree, only in the proof body
of an audited theorem or lemma, and only when the declaration has a corresponding Blueprint node.
Never use `sorry` to fill a definition or instance or to conceal a statement-elaboration problem.
The default branch, any completion commit, and every handoff must contain zero `sorry`.

### 3. Build and audit the dependency DAG

Add reviewed `uses :=` edges for the mathematical dependencies of each statement. These edges are
the conceptual proof DAG, not the Lean import graph or a UI-progress mechanism. Do not add false
edges to manipulate readiness or status. Update the node in the same change whenever its formal
statement, representation mapping, declaration association, or mathematical dependencies change.

### 4. Close dependency-ready leaves

Prove only nodes whose dependencies are closed. Reuse earlier FABL and Mathlib results before adding
helpers, eliminate temporary `sorry`s bottom-up, and run the narrow module build after each small
patch. Do not force proof work into book order when the DAG says a prerequisite is missing.

### 5. Close the chapter

After all leaves are closed, rerun a statement-fidelity audit against the book, the root build and
forbidden-token gate, the strict Blueprint build, and any affected HTML/PDF visual checks. A chapter
is complete only when every in-scope node is exact or explicitly documented as a generalization,
all associated declarations are present and proved, and the entire dependency closure passes.

## Agent task contract

Each prover task should cover one DAG leaf or a tightly coupled helper cluster. State the target
declaration, allowed files and imports, immutable statement and representation choices, narrow build
command, and completion criteria. Statement extraction, reuse audit, proof construction, error
repair, and final fidelity audit are separate responsibilities even when one agent performs several
of them sequentially.

- Do not let parallel agents edit the same production module or Verso section.
- Do not alter a target statement, representation, or Blueprint edge merely to make a proof pass.
- Search before inventing; every helper must be used by the production proof that motivated it.
- If blocked, report the exact goal, searched FABL/Mathlib declarations, attempted approaches, and
  the smallest proposed missing lemma. Do not leave speculative APIs or unrelated refactors.

## Proof and code policy

- `admit`, project-defined `axiom`, `unsafe`, and `native_decide` are forbidden at every stage.
- Do not add a global simplifier attribute to repair one local proof.
- Do not disable heartbeat limits globally.
- Use Mathlib naming, documentation, formatting, imports, and canonical normal forms.
- Keep foundational proofs readable; use automation where it shortens a stable, well-scoped step.
- Proofs live only in production Lean declarations. Do not add prose proof blocks to the Blueprint.
- Every production module document states the exact original-book items implemented in that file.
  Use a range only when the associated items are genuinely consecutive; otherwise list them. A
  stable aggregate names its book section, and infrastructure with no book-facing declaration says
  so explicitly. Derive this metadata from Blueprint declaration associations rather than guessing.

## Blueprint contract

Each in-scope book item must have one complete human-readable statement, real compiled declarations,
fidelity metadata, and reviewed `uses` dependencies. The site uses the official Verso Blueprint UI
and default `blueprint` theme. Project CSS may join the statement and generated Lean declaration
panel into one visual card, but must not replace or duplicate official tags, declaration status,
`uses`/`used by`, summary, or graph controls.

Never edit `blueprint-verso/_out/`. When adding a chapter, update its Verso aggregate imports and the
strict manifest expectations in `blueprint-verso/scripts/site.sh` in the same change. The current
Chapter 1 baseline is 43 nodes (34 primary and 9 support), 111 associated Lean declarations, and 62
reviewed dependency edges.

The completed Chapter 2 baseline is 78 nodes (64 primary and 14 support), 240 associated Lean
declarations, and 183 reviewed dependency edges across Sections 2.1--2.5. The aggregate Chapters
1--2 baseline is 121 nodes, 351 unique declaration associations, and 245 edges.

The completed Chapter 3 baseline is 62 nodes (43 primary and 19 support), 399 associated Lean
declarations, and 164 reviewed dependency edges across Sections 3.1--3.5. The aggregate Chapters
1--3 baseline is 183 nodes, 750 declaration associations, and 409 edges.

Include every inventoried chapter in `Blueprint.lean` and `Book.lean` throughout its active proof
phase so the official diagram exposes unfinished nodes and their formalization status. Keep the
section and aggregate sources buildable, and update the manifest expectations to cover the complete
inventory. A missing `lean :=` association is the honest representation of an unfinished node;
never attach a placeholder declaration or weaken a statement to manufacture a completed status.
Chapter completion still requires every node to have honest compiled declaration associations and
the complete dependency closure to be proof-complete.

Verso owns chapter and section numbering. Document titles must contain only their prose title: do
not prefix them with `Chapter N`, `Section N.M`, or a handwritten number, and do not repeat a
document title as an immediately nested heading.

## Build and verification flow

Run dependency setup only after the first clone or an intentional toolchain/dependency change:

```bash
lake update
lake exe cache get
cd blueprint-verso
lake update
lake exe cache get
```

During proof development, build the narrowest affected production module:

```bash
lake build FABL.Chapter01.BasicFourierFormulas
```

When parallel agents share one checkout and Lake build tree, preserve the last green `.olean` of
every upstream module. Compile an experimental edit to temporary outputs first, for example:

```bash
lake env lean FABL/Chapter03/LearningTheory.lean \
  -o /tmp/fabl-learning.olean -i /tmp/fabl-learning.ilean
```

Only after that command succeeds may the owning agent run the narrow `lake build` to promote the
artifact. Never launch a downstream or Blueprint Lake build while an upstream production source is
between green checkpoints: Lake correctly invalidates the dependency, and a failed rebuild removes
the shared last `.olean`, blocking every other agent. Prefer isolated worktrees/build directories
when parallel tasks cannot respect this checkpoint discipline.

During Blueprint development, build the affected section before rendering the complete site:

```bash
cd blueprint-verso
lake build +FABLBlueprint.Chapter01.Section04
```

Before a chapter handoff, run from the repository root:

```bash
lake build
if rg -n --glob '*.lean' \
  '\b(sorry|admit|axiom|unsafe|native_decide)\b' FABL FABL.lean
then
  exit 1
fi
cd blueprint-verso
./scripts/site.sh build
```

`site.sh build` already runs the strict manifest validator and `vbp check`. Run
`./scripts/site.sh pdf` when book/PDF rendering changed, and inspect HTML through
`./scripts/site.sh serve` rather than `file://` when browser behavior changed.

Lake builds are incremental. The reported job count is the checked dependency-graph size, not the
number of modules recompiled. Verso 4.30 still performs a complete site traversal when HTML is
rendered; its generated preview cache is not an incremental build cache.

The root `FABL.lean` must import every production module. A file unreachable from that root is not
part of the verified library.

## Version-control boundaries

- Never stage or commit the O'Donnell book PDF, `.lake/`, `tmp/`, browser QA output, or generated
  Blueprint `_out/` artifacts. Never bypass these rules with `git add -f`.
- Track the Lean sources, Verso sources, `lean-toolchain`, Lake configuration and manifests, CI,
  scripts, and project documentation.
- Do not commit, push, add a remote, or rewrite history unless the user explicitly requests it.
- Before a first or release commit, verify the book is ignored and inspect the complete staged file
  list.
