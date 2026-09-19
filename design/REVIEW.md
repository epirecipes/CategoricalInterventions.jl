---
title: "Review: CategoricalInterventions.jl and *Temporal sheaf theory for reconciling temporal complexity within public health modeling*"
subtitle: "Overlap, uniqueness, and a critical assessment of the package against its own design note"
author: "Prepared for Simon Frost"
date: "2026-09-19"
---

# Scope and method

This review covers three documents:

1. **The package** `CategoricalInterventions.jl` (v0.1.0): all source (`src/`, `ext/`), the Documenter manual (`docs/src/`), the seven Quarto vignettes, the test suite, and the Lean 4 proof directory.
2. **The design note** `papers/category_theory_interventions.md`, which the package README claims to implement.
3. **The paper** `papers/ACT_2026_paper_51.pdf`: Niu, Osgood, Zelko and Srinivasan, *Temporal sheaf theory for reconciling temporal complexity within public health modeling*, submitted to ACT 2026. Text and formulas were extracted with `opendataloader-pdf`.

Verification performed:

| Check | Result |
|---|---|
| `lake build` in `proofs/` (Lean 4.11.0, no Mathlib) | Builds; 9 theorems, all closed |
| `Pkg.test()` on Julia 1.12.7 | 76 of 76 pass |
| Manual read of every source, doc, and vignette file | Complete |

# Summary

The package is a well-engineered *scheduling and callback* library with a thin categorical layer. Its real strengths are a clear data model (typed targets, half-open supports, effects, explicit combination algebras), a sound conflict rule, and a lowering to SciML callbacks that is demonstrated identically across AlgebraicPetri, StockFlow, and AlgebraicDynamics, with numerical cross-checks. Its categorical content, however, consists of one `FinFunction` and one flat, stringified ACSet, and its Lean proofs cover only list-append laws and two one-line compatibility facts. The README's claim to "implement the framework sketched in" the design note is about one-third fulfilled (see the claim table in Section 4.8).

The paper is a theory of *time-varying data*: narratives as sheaves on an interval site, the topos structure of discrete narratives, an internal logic of temporal truth values, timescale-changing geometric morphisms, and temporal graphs, applied to contact tracing and prevalence over intervals in agent-based models. It never mentions interventions, parameters, or compartments.

The two are complementary rather than competing. They share the interval-poset foundation, the "narrative" vocabulary from Bumpus et al., and the Catlab toolchain. The paper supplies precisely the sheaf-theoretic and logical content that the design note asks for and the package currently gestures at without implementing. Section 7 lists the concrete bridges; the companion document `PLAN.md` turns them into a development plan.

# The three documents

## The design note

The note proposes: time as a site of intervals; persistent narratives (sheaves) for schedules and cumulative narratives (cosheaves) for logs; intervention atoms as local edits with a target, support, effect, and mode; interventions as morphisms of a *partial* category whose composition is defined only when local edits glue; five compatibility rules (different targets commute; same target with disjoint supports glues; same target with overlap needs an algebra; overlapping absolute assignments conflict by default; state edits must preserve invariants); epochization as a functorial normal form; discrete and continuous semantics; interventions as lenses; transport of interventions along model morphisms (for example from an unstratified to an age-stratified model); and seven open design questions.

## The package

An `InterventionAtom` is an identifier, a `Target` (name, kind in {Parameter, State, Process, Observation}, value type, combination algebra), a half-open `Interval`, an effect (`SetValue`, `Add`, `Scale`, `MapEffect`), and metadata. An `InterventionProgram` is a vector of atoms. `compose_interventions` concatenates and rejects same-target overlaps that the target's algebra cannot combine. `epochize` refines all endpoints into epochs with combined effects. `apply_interventions` and `apply_discrete` evaluate a program against scalar and vector baselines. `to_callback` lowers a program to a `PresetTimeCallback`: parameter-like targets are interval effects (reset targeted selectors to baseline, then apply what is active); state targets are pulses at the support start. `PetriIndexing` maps target names to `integrator.u` and `integrator.p` selectors, labelled or positional. A Unicode layer (`ℙ 𝕊 𝕀 ι Π ≜ δ κ ⊕ ⊙`) wraps the constructors.

## The paper

The paper specializes Bumpus, Fairbanks, Karvonen, Leal and Simard's narratives to a totally ordered timeline τ. With $I_\tau$ the poset of closed intervals $[a,b]$ under containment and the Johnstone coverage $\{[a,p],[p,b]\}$ of $[a,b]$, a **persistent** $D$-narrative is a sheaf $X: I_\tau^{op} \to D$, characterized by the pullback

$$X[a,b] \cong X[a,p] \times_{X[p,p]} X[p,b],$$

and a **cumulative** narrative is a cosheaf with the dual pushout. Section 2 establishes:

- **Discrete narratives** (τ = ℤ) are presheaves on the zigzag category $\mathcal{Z}$ of subunit intervals $[t]$ and $[t,t+1]$ (Prop. 2.3), and $\mathcal{Z} \cong \mathcal{Z}^{op}$ (Prop. 2.4), so persistent and cumulative coincide up to this isomorphism. $\mathcal{Z}^{op}$ is the category of elements of the infinite path graph, so $[\mathcal{Z}^{op},\mathbf{Set}] \simeq \mathbf{Grph}/P_\mathbb{Z}$ (Prop. 2.6, Cor. 2.7).
- **Timescale change**: a monotone $r: \tau' \to \tau$ induces a geometric morphism $\mathrm{Pe}_{\tau'}(\mathbf{Set}) \to \mathrm{Pe}_\tau(\mathbf{Set})$ iff every $c \in \tau'$ is bracketed by the image of $r$ (Prop. 2.8). Sampling ℝ at ℤ is the example.
- **Topos structure** of $[\mathcal{Z}^{op},[C,\mathbf{Set}]]$: explicit exponentials (Prop. 2.13) and subobject classifier (Prop. 2.15). For $C = 1$, $\Omega[t,t+1]$ has five elements: false throughout; true at $t$ only; true at $t+1$ only; true at both endpoints but not throughout; true throughout. The Heyting algebra of subobjects is proposed as a temporal query language and is computed with Catlab's `subobject_classifier` and `⟹`.
- **Temporal graphs**: complete graphs form a reflective subcategory (Prop. 2.18); a graph is complete iff it is isomorphic to its exponential by the representable vertex (Prop. 2.19); temporal cliques are defined via exponentials (Def. 2.20); prefix/suffix pushouts of path graphs stay path graphs (Lemma 2.23); temporal paths are natural transformations from a path-shaped cosheaf (Def. 2.25).

Section 3 applies this to contact tracing (a temporal path from A to C witnesses that A could have infected C, found by hom-search) and to prevalence over intervals in an agent-based model (persistent = "had the condition throughout", a pullback; cumulative = "had it at some point", a pushout). Section 4 lists as future work the internal quantifiers, the use of geometric morphisms for cross-timescale comparison, and pedagogy.

# Package review

## Architecture

The package is small (about 740 lines of core Julia, 60 in the extension), dependency-light (Catlab and Dates, with DiffEqCallbacks as a weak dependency), and cleanly layered: data model, validation, epochization, application, callback lowering, Catlab export, Unicode sugar. The extension mechanism is used correctly. The vignettes are reproducible Quarto documents with pinned environments for the two frameworks with tighter compatibility bounds.

## Correctness findings

Numbered for reference in the plan. Severity: **H** likely to mislead users or break composition, **M** wrong but bounded, **L** cosmetic.

1. **(M) Conflict reports inside `_combine_active` name the same atom twice.** At `src/CategoricalInterventions.jl:373` and `:378` the `Conflict` is built as `Conflict(existing, atom.support, atom, atom, ...)`, so the user sees one atom as both `left` and `right`, and the overlap is the whole support of the second atom rather than the intersection. `conflicts` at `:319` reports correctly; the fold path does not.
2. **(M) `check=false` is not honored by `epochize`.** `epochize(program; check=false)` at `:395` skips the pairwise check but `_combine_active` throws anyway on any overlap it cannot combine, so the keyword cannot be used to inspect a conflicting program.
3. **(M) Target identity ignores the algebra, but conflict detection depends on it.** `==` and `hash` at `:197` use only name and kind, so `Target(:beta) == Target(:beta; algebra=MultiplicativeAlgebra())` is `true` (and the test suite asserts this). The algebra is then compared by `typeof` at `:305`, and the fold at `:366` silently adopts whichever target instance was seen first. Consequence: the algebra must be re-declared at every construction site, and two mentions of the "same" target with different algebras are a conflict with a confusing message. The algebra is a property of the model's target space, not of an atom.
4. **(M) State pulses carry a meaningless stop time.** `Interval` at `:58` requires `start < stop`, so a pulse must be written as `Interval(15.0, 16.0)` and the `16.0` is ignored by `callback_times` (`:542`) and `state_pulses_at` (`:576`). The vignettes work around this with `Interval(15.0, 15.0 + δt)`. An instant is not an interval, and the design note's distinction between pulses and flows is collapsed.
5. **(M) The callback caches baselines per integrator object forever.** The extension keeps an `IdDict` keyed by integrator (`ext/...Ext.jl:30`). It is never cleared, so many solves with one callback leak, and `reinit!` on the same integrator with new parameters reuses the stale baseline.
6. **(L) Composition with `LatestWins` is not commutative**, since `_combine_active` folds in program order. The manual's description of `⊕` as composition does not state this, and the Lean file proves associativity only for raw append.
7. **(L) `as_acset` stringifies every attribute** (`:719`), so the ACSet cannot be used for any computation: no numeric comparison, no data migration, no functorial operations. It is a display table.
8. **(L) `callback_times` returns `Any[]`** (`:543`), which is type-unstable and returns mixed `Int`/`Float64` when supports have mixed element types.
9. **(L) The README points to `../category_theory_interventions.md`**, which lives at `papers/category_theory_interventions.md`.

Nothing above affects the numerical results in the vignettes, which are correct for the cases exercised.

## Design assessment

- **The conflict rule is right and is the package's best idea.** Rejecting same-target overlaps unless an algebra is declared makes composition honest. It is exactly the design note's Rules 1 to 4.
- **Parameters and states have different semantics but the same type.** Parameter-like targets are interval effects with reset-to-baseline; state targets are pulses. The distinction is buried in `if atom.target.kind == State` branches. This is the persistent/cumulative distinction of the paper and the note, and it deserves to be a type.
- **No model object.** Targets float free of any model. The user must build a `PetriIndexing` by hand and repeat algebras on every target. There is no way to ask "what targets does this model have?" or to check that a program is well-typed against a model before solving.
- **No morphisms.** The package has objects (programs) and a partial monoid, but nothing maps programs between models. The design note's transport along model morphisms, and its restrict/glue operations, are absent.
- **The categorical layer does not carry weight.** `epoch_finfunction` is a lookup table wrapped in a `FinFunction`; `as_acset` is a stringified table. No functoriality, no sheaf condition, no restriction maps, nothing is computed *with* the categorical structure.
- **The Unicode DSL is pleasant but exposes the internals.** A user must know about targets, algebras, and atoms to write `ι(:closure, ℙ(:beta; algebra=MultiplicativeAlgebra()), 𝕀(10,30), κ(0.6))`. The audience that does not want the mathematics needs `scale(:beta, 0.6; during=(10,30))`.

## Documentation

The Documenter manual is accurate, concise, and complete for the exported surface (`checkdocs=:exports` is enforced). The categorical page is honest that the Catlab representations are "for inspection and bookkeeping". The manual would benefit from a one-page "semantics" statement: exactly what a program *means* as a function of time, and what the callback guarantees.

## Vignettes

Vignettes 1 to 3 are clear introductions. Vignettes 4 to 7 tell the same lockdown-plus-vaccination SIR story in four frameworks. That is a good demonstration of *framework independence* and the cross-checks are valuable, but nothing in them shows the power of a categorical approach: no abstraction over models, no composition of models with interventions, no morphism, no transport, no query. Four near-identical vignettes is also a maintenance burden; they should be one vignette parameterized by framework, and the freed space used for vignettes that demonstrate structure.

## Tests

76 assertions with good coverage of the core: intervals, epochization, algebras, value types, discrete schedules, Unicode operators, callback helpers with a fake integrator, baseline reuse across solves, and an AlgebraicPetri integration test. Gaps: `LatestWins` is never tested; `Process` and `Observation` kinds are never tested; the success path of `MapEffect` is never tested; `epochize(check=false)` is never tested; the conflict *reports* (finding 1) are never inspected. There are no property-based tests, which the algebraic laws invite.

## Lean proofs

The proofs build (`lake build`, Lean 4.11.0, no Mathlib). They contain 9 theorems in 156 lines: four interval facts over `Nat`, three list-append monoid laws, and two compatibility facts that are direct unfoldings of the definitions. They do not model effects, algebras, epochs, application, or callbacks, so they verify nothing about the package's semantics. The README table listing them under "Formal proofs" is accurate about what is proved, but a reader could reasonably infer more than is there. The honest description is "a Lean sketch of the interval combinatorics".

## Claims in the design note versus the package

| Design-note claim | Status in v0.1.0 |
|---|---|
| Time as an interval poset; half-open convention | Implemented |
| Persistent narrative (sheaf) of model specification | Not implemented; epochs are a partition table |
| Cumulative narrative (cosheaf) of intervention log | Not implemented |
| Atoms with target, support, effect, mode, metadata | Implemented |
| Rules 1 to 4 (commute, glue, algebra, reject absolute overlap) | Implemented |
| Rule 5 (state edits preserve invariants) | Not implemented; conservation only by user discipline |
| Epochization, functorial refinement | Implemented; functoriality not stated or proved |
| Discrete-time semantics; pre/post-update pulse ordering | Partially; ordering convention undocumented |
| Continuous-time: parameter intervals, state pulses | Implemented |
| Continuous-time: vector-field intervals, state flows | Not implemented |
| Interventions as partial-category morphisms | Partial monoid on programs only; no morphisms between models |
| Interventions as lenses | Not implemented |
| `restrict`, `glue`, `discretize` operations | `discretize` yes (as `apply_discrete`); `restrict`, `glue` no |
| Transport along model morphisms (stratification) | Not implemented |
| Structured conflict reports with `required_algebra` | Partially (finding 1; no `required_algebra`) |
| Provenance and priority in resolution | Metadata field exists; unused |
| Uncertainty in effects | Not addressed |

# Overlap between the paper and the package

1. **Same lineage and vocabulary.** Both descend from Bumpus et al.'s narratives. The design note cites that paper directly; the ACT paper extends it. Both use Catlab's `@present` and `@acset_type`.
2. **Intervals as the organizing structure.** The paper's site is the containment poset of closed intervals with the Johnstone coverage. The package's epochs are the coarsest partition refining all supports. Epochization is the concrete shadow of the paper's covering families.
3. **Gluing and compatibility.** The sheaf condition glues data on $[a,p]$ and $[p,b]$ iff they agree at $p$. The package's conflict rule is a value-level version: two `Scale` effects overlapping on $[20,30)$ cannot both be sections of one "value of beta" narrative, so composition is rejected; declaring a multiplicative algebra changes the glued object from a value to a factor, where gluing succeeds. `RejectOverlap` is a gluing failure, precisely as the design note says.
4. **Persistent versus cumulative.** The paper's "throughout an interval" (pullback) against "at some time in an interval" (pushout) is the package's parameter-interval against state-pulse split, expressed there as an `if` on target kind.
5. **Discrete sampling.** `epoch_finfunction` and `apply_discrete` are object-level restrictions of a continuous narrative along ℤ → ℝ; the paper's Example 2.9 is the same operation, and Prop. 2.8's bracketing condition is the mathematical reason for the package's runtime error when a sampled time falls outside every epoch.

A precise observation that links the two: for a **single atom** with convex support, the paper's fifth truth value on $[t,t+1]$, "true at both endpoints but not throughout", is unreachable, because an interval containing $t$ and $t+1$ contains everything between. For a **target** under a program of several atoms it is reachable, for instance two disjoint closures on `:beta` ending and starting inside the unit interval. So the paper's $\Omega$ distinguishes atoms from targets in a way the package's epoch table cannot express.

# Uniqueness

**Unique to the paper.** The sheaf and cosheaf conditions and their equivalence with presheaves on $\mathcal{Z}$; the topos structure with explicit exponentials and subobject classifier; the internal logic as a query language; timescale-changing geometric morphisms and their characterization; temporal cliques and paths; individual-level applications to contact tracing and ABM prevalence; pen-and-paper proofs of every proposition. Its Catlab code is illustrative (a two-point $\mathcal{Z}$ and its subobject lattice) rather than a pipeline.

**Unique to the package.** Interventions as first-class objects with effect algebras and conflict detection; typed targets with value types; lowering to executable SciML simulations across three AlgebraicJulia modelling frameworks with cross-checks; discrete `FunctionMap` support; a Unicode DSL; machine-checked (if small) proofs; reproducible vignettes. Its level of description is population-aggregate parameters and states, not individuals.

**Neither has.** A model object with a declared target space; morphisms between models and transport of interventions along them; state flows as added processes; invariants; a semantics statement that is proved rather than illustrated.

# Bridges

These are the points at which the paper's ideas make the package's claims true rather than aspirational. Each is developed in `PLAN.md`.

1. **An intervention program *is* a persistent narrative.** Let $A(I)$ be the set of atoms whose support contains the closed interval $I$. Then $A[a,b] = A[a,p] \cap A[p,b]$ for $a \le p \le b$, which is the sheaf condition for a subsheaf of the constant sheaf on the atom set. Dually, $C(I)$ = atoms whose support *meets* $I$ satisfies $C[a,b] = C[a,p] \cup C[p,b]$ with $C[a,p] \cap C[p,b] = C[p]$, by convexity. Both are elementary and provable in Lean without any topos machinery. Epochs are the level sets of $A$. This gives the package the narrative it names.
2. **Application is a natural transformation.** The schedule sheaf $\Theta(I) = \{\text{functions } I \to V\}$ is a persistent sheaf, and a conflict-free program acts on it pointwise, so application commutes with restriction. That is the sense in which "interventions are morphisms of narratives", and it is a one-line naturality proof once effects are monoid actions.
3. **Timescale change is pullback of presheaves.** Sampling, `saveat` grids, and discrete `FunctionMap` models are all $r^*$ for a monotone $r$. The theorem "apply then sample equals sample then apply" makes the four SIR vignettes a corollary rather than a coincidence.
4. **The five truth values give intervention queries.** Encoding a finite window of $\mathcal{Z}$ as an ACSet, as in the paper's Listing 1, and a program's active-atom sheaf as an instance, makes Catlab's subobject lattice and Heyting operations available: "some NPI in force throughout week $k$" against "at some point in week $k$", and implications between programs.
5. **Individual-level interventions.** On an ABM contact narrative in $[\mathcal{Z}^{op},\mathbf{Grph}]$, a lockdown is a subobject (keep household edges on the closure interval) and a vaccination is a morphism of the infected-individual narrative. This extends the package from compartmental targets to the paper's data.

# Appendix A: verification log

- **Lean.** `cd proofs && lake build` on `leanprover/lean4:v4.11.0`: `Build completed successfully.` All 9 theorems close without `sorry`.
- **Julia.** `julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'` on Julia 1.12.7: all 76 tests pass in 12 s (`Test Summary: CategoricalInterventions.jl | Pass 76 Total 76`).
- **Paper extraction.** `opendataloader-pdf 2.5.8` in a local venv produced 53 KB of Markdown and text plus five figure images. Formulas in the appendix proofs were partially garbled by the extractor (subscripts and diagram layouts); the body text, definitions, propositions, and listings were recovered cleanly and are the basis of Section 3.3.
