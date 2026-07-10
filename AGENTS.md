# FABL contributor contract

## Mission and sources of truth

FABL formalizes the May 2021 arXiv edition of Ryan O'Donnell's *Analysis of Boolean Functions* in
Lean 4 and Mathlib. The first release target is complete coverage of Chapters 1 and 2.

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
- Do not introduce one global Boolean-cube representation. Use the domain stated by each theorem and
  add an explicit bridge only when a production theorem crosses representations.
- Keep mathematical definitions and proofs pure. Extraction, rendering, validation, PDF generation,
  and CI belong at the repository edge.
- Do not add `Core`, `Common`, `Utils`, or `ToMathlib` dumping grounds. Extract a shared declaration
  only when a real downstream theorem needs it; prefer the narrowest mathematically meaningful home.
- `lean-booleanfun` is cited prior art and a search aid, not an upstream dependency. Do not import,
  vendor, or copy it. Validate every reuse idea against Mathlib and FABL.

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

## Blueprint contract

Each in-scope book item must have one complete human-readable statement, real compiled declarations,
fidelity metadata, and reviewed `uses` dependencies. The site uses the official Verso Blueprint UI
and default `blueprint` theme. Project CSS may join the statement and generated Lean declaration
panel into one visual card, but must not replace or duplicate official tags, declaration status,
`uses`/`used by`, summary, or graph controls.

Never edit `blueprint-verso/_out/`. When adding a chapter, update its Verso aggregate imports and the
strict manifest expectations in `blueprint-verso/scripts/site.sh` in the same change. The current
Chapter 1 baseline is 41 nodes (34 primary and 7 support), 103 associated Lean declarations, and 59
reviewed dependency edges.

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
