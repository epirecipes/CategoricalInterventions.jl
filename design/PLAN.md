---
title: "A categorical framework for interventions: development plan for CategoricalInterventions.jl"
subtitle: "From a scheduling library to a verified, compositional theory of model edits that ordinary modellers can use"
author: "Prepared for Simon Frost"
date: "2026-09-19"
---

# Principles

1. **One core, two doors.** A plain API (`scale`, `transfer`, `during`, `simulate`) for modellers, and a categorical API (`persistent`, `transport`, `lift`, `throughout`) for researchers. The plain API is *defined in terms of* the categorical core, not a parallel implementation, so the two can never disagree.
2. **Every claim is backed.** A categorical word appears in the documentation only if it names a Julia definition, a Lean theorem, and a test. Section 8 is the ledger. Anything not on the ledger is described as a convenience, not as mathematics.
3. **Honesty about what is proved.** Lean verifies the *algebra and combinatorics* of programs, their semantics on schedules, and the lowering algorithm. It does not verify ODE solvers, Catlab internals, or floating point. The docs say so in one sentence on the front page.
4. **Novelty with a purpose.** Five results are new relative to the paper, the design note, and v0.1, and each buys a user-visible capability: programs as subsheaves (queries), application as a natural transformation (framework independence as a theorem), transport along model morphisms (define once, stratify for free), flows by augmentation (vaccination campaigns without new solver machinery), and inference of programs from schedules (recover interventions from fitted time-varying parameters).

# Mathematical core

This section is the specification. Julia implements it; Lean proves it. Notation is chosen so that each definition has an obvious name in both.

## Timeline and supports

Let $\tau$ be a linear order (ℝ, ℤ, or a finite grid). A **span** is a half-open interval $[a,b)$ with $a<b$. An **instant** is a point $\{t\}$. A **support** is a span or an instant. Every support is a *convex* subset of $\tau$: if $x \le y \le z$ and $x, z \in S$ then $y \in S$. Convexity is the only property the theory needs; it is what makes the cumulative gluing condition (Section 2.4) hold.

Closed intervals $[a,b]$ (allowing $a=b$) are used only to *evaluate* narratives; they are never supports. This resolves the half-open versus closed tension between the package and the paper: supports are half-open so that epochs partition time, and narratives are evaluated on the paper's closed-interval site.

Design decision (note's open question 1): keep $[a,b)$. Pulses become genuine instants, fixing review finding 4.

## Targets and effect algebras

A **target space** $T$ is a finite set. Each $j \in T$ carries a value object $V_j$ and an **effect algebra** $E_j$, which is a **partial commutative monoid** (PCM) acting on $V_j$:

- a unit $1 \in E_j$ and a partial product $e \cdot e' \in E_j \cup \{\bot\}$ that is commutative and associative where defined, with $1 \cdot e = e$;
- an action $e \triangleright v \in V_j$ with $1 \triangleright v = v$, and, for the *acting* algebras (`Reject`, `Multiplicative`, `Additive`, `Cap`, `Floor`), $(e \cdot e') \triangleright v = e \triangleright (e' \triangleright v)$ whenever $e \cdot e'$ is defined. `Affine` has an action but not this law; see below.

PCMs are the standard structure for "compose when compatible" (they underlie separation logic), and they make the design note's Rules 1 to 4 instances of one definition rather than four special cases. The shipped instances:

| Algebra | Elements | Product | Defined when | Action |
|---|---|---|---|---|
| `Reject` | $\{1\} \cup E$ | $1 \cdot e = e$ | one factor is $1$ | given |
| `Multiplicative` | $\mathbb{R}_{>0}$ | product | always | $v \mapsto ev$ |
| `Additive` | $(G,+)$ | sum | always | $v \mapsto v+e$ |
| `Cap` / `Floor` | semilattice | $\min$ / $\max$ | always | $v \mapsto \min(v,e)$ |
| `Affine(M)` | $\mathrm{Option}(V_j) \times M$ | see below | at most one absolute | see below |

`Affine(M)` is the principled answer to the note's open question 4 (how absolute and relative effects combine). Its elements are an optional absolute value plus a relative effect from a PCM $M$; $(a,m)\cdot(a',m')$ is defined iff $a$ or $a'$ is absent, giving $(a \vee a', m \cdot m')$; and $(a,m) \triangleright v = m \triangleright (a \text{ if present else } v)$. Two overlapping absolute assignments are a conflict (Rule 4); an absolute assignment with any number of scalings is not, and means "set, then scale". This is a PCM (`affine_pcm`), but its action is *not* a monoid action: the absolute value is applied first and the relative product second regardless of program order (`affine_action`), so $\mathrm{act}(a \cdot b) = \mathrm{act}(a) \circ \mathrm{act}(b)$ holds only when $b$ carries no absolute value (`affine_act_mul_of_relative`). Lean proves exactly these statements.

Ordered policies (`LatestWins`, `HighestPriority`) are **not** PCMs, because they are not commutative. They are shipped as a separate class `OrderedPolicy` whose product uses program order or a priority key from atom metadata, and the documentation states that composition under an ordered policy depends on order. This fixes review finding 6 by making it a type distinction rather than a footnote.

Effect algebras are declared **once per target on the model**, never on atoms (fixing finding 3). Defaults: `Reject` for any target without a declaration; models constructed from AlgebraicPetri or StockFlow declare `Affine(Multiplicative)` on rates, because rates are positive reals with a canonical monoid, and `Additive` on states.

## Programs, active sets, conflict-freeness

An **atom** is $(id, j, S, e)$ with target $j \in T$, support $S$, effect $e \in E_j$, plus metadata. A **program** is a finite list of atoms. Lists rather than sets so that ordered policies are meaningful; under PCMs the order is provably irrelevant.

$\mathrm{active}(P,t)$ is the sublist of atoms whose support contains $t$. For each target $j$, $\mathrm{fold}_j(P,t)$ is the PCM product of the effects of active atoms on $j$, which is either an element of $E_j$ or $\bot$. $P$ is **conflict-free** iff $\mathrm{fold}_j(P,t) \ne \bot$ for all $t, j$.

Theorem (pairwise suffices): for every shipped PCM, $\mathrm{fold}_j(P,t)$ is defined iff every pair of active atoms on $j$ has a defined product. This is what licenses the $O(n^2)$ pairwise check in `conflicts`; it is proved per instance, not assumed.

A **conflict report** is $(j, S_1 \cap S_2, a_1, a_2, \text{reason}, \text{required})$ where `required` names an algebra whose declaration would resolve it. This fixes finding 1 and implements the note's `required_algebra`.

## Narratives: programs as sheaves and cosheaves

For a closed interval $I$ define

$$\mathcal{A}_P(I) = \{a \in P : I \subseteq S_a\}, \qquad \mathcal{C}_P(I) = \{a \in P : I \cap S_a \neq \emptyset\}.$$

$\mathcal{A}_P$ is the **persistent narrative** of $P$: the atoms in force *throughout* $I$. It is contravariant ($I \subseteq J \Rightarrow \mathcal{A}_P(J) \subseteq \mathcal{A}_P(I)$) and satisfies, for $a \le p \le b$,

$$\mathcal{A}_P[a,b] = \mathcal{A}_P[a,p] \cap \mathcal{A}_P[p,b],$$

which is the sheaf condition for the Johnstone coverage (the pullback over $\mathcal{A}_P[p,p]$ of two subsets of a fixed set is their intersection). So $\mathcal{A}_P$ is a subsheaf of the constant sheaf on the atom set, an object of the paper's $\mathrm{Pe}_\tau(\mathbf{Set})$.

$\mathcal{C}_P$ is the **cumulative narrative**: atoms in force *at some time* in $I$. It is covariant and satisfies

$$\mathcal{C}_P[a,b] = \mathcal{C}_P[a,p] \cup \mathcal{C}_P[p,b], \qquad \mathcal{C}_P[a,p] \cap \mathcal{C}_P[p,b] = \mathcal{C}_P[p,p],$$

the second by convexity of supports. Together these say the pushout square is a union glued along the shared point, which is the cosheaf condition.

**Epochs** are the level sets of $t \mapsto \mathrm{active}(P,t)$, computed from the sorted endpoints exactly as v0.1 does. Theorem (epoch constancy): $t, t'$ in the same epoch implies $\mathrm{active}(P,t) = \mathrm{active}(P,t')$. Theorem (refinement is functorial): the epochs of $P \,\#\, Q$ refine the epochs of $P$.

These are the design note's "persistent narrative of model specification" and "cumulative narrative of intervention log", now as definitions with theorems rather than aspirations. No Grothendieck topology is formalized; the docs state the two equations and cite the paper's Definition 2.1 for why they are the sheaf and cosheaf conditions.

## Semantics on schedules

A **schedule** is a function $\theta: \tau \to \prod_j V_j$. A conflict-free program acts pointwise:

$$(P \triangleright \theta)(t)_j = \mathrm{fold}_j(P,t) \triangleright \theta(t)_j.$$

Theorems:

1. **Identity.** $[\,] \triangleright \theta = \theta$.
2. **Locality.** If no atom is active at $t$ then $(P \triangleright \theta)(t) = \theta(t)$.
3. **Homomorphism.** If $P \,\#\, Q$ is conflict-free then, for the acting algebras, $(P \,\#\, Q) \triangleright \theta = Q \triangleright (P \triangleright \theta) = P \triangleright (Q \triangleright \theta)$ (`apply_append`). Under `Affine` the composite still does not depend on the order of atoms (`apply_comm`, which holds for every PCM), but sequential application agrees with the composite only when the later program is purely relative (`apply_append_affine`): absolute assignments always apply first.
4. **Naturality.** For any $r: \tau' \to \tau$, $(P \triangleright \theta) \circ r = (r^*P) \triangleright (\theta \circ r)$, where $r^*P$ has supports $r^{-1}(S_a)$. In words: application commutes with restriction and with resampling. Restriction to a sub-interval is the case $r$ = inclusion, and this is the statement that $P \triangleright -$ is a **natural transformation** of the schedule sheaf $\Theta(I) = \{I \to \prod V_j\}$.
5. **Grid sampling.** For $r(k) = t_0 + k\Delta$ the preimage of a span is a span with ceiling endpoints, so $r^*P$ is again a program over ℤ. This is the theorem behind `apply_discrete` and behind using one program for both ODE and `FunctionMap` models.
6. **Piecewise constancy.** If $\theta$ is constant on each epoch of $P$ then so is $P \triangleright \theta$.

Theorem 4 is what the paper's Example 2.9 becomes for interventions. We claim only pullback of presheaves along $r$; the paper's Proposition 2.8 (when $r^*$ is part of a geometric morphism) is cited for readers who want the topos-level statement, and is relevant to Section 2.8 but not to correctness of schedules.

## Models, dynamics, and the three kinds of intervention

A **model** is $(T, \text{dynamics}, \text{invariants}, \text{indexing})$: a target space split into parameters and states, a dynamics object owned by the host framework, a list of invariants, and the selectors that locate each target in the integrator's `p` and `u`. Models are constructed automatically from AlgebraicPetri nets, StockFlow diagrams, AlgebraicDynamics systems, and (new) ModelingToolkit systems, each in its own extension; the plain user never writes a `PetriIndexing`.

Interventions on a model are of three kinds, matching the note's table:

| Kind | Support | Acts on | Semantics |
|---|---|---|---|
| **Parameter interval** | span | schedule $\theta$ | Section 2.5 |
| **State pulse** | instant | state $x(t^-) \mapsto x(t^+)$ | rewrite at an instant, checked against invariants |
| **State flow** | span | dynamics | reduced to a parameter interval on an augmented model |

**Pulses** are `Set`, `Add`, or `Transfer(j \Rightarrow j', n)`. A transfer is one atom, not two paired `Add`s, and preserves any conservation invariant by construction. Invariants (`Conserved([:S,:I,:R])`, `Nonnegative(:S)`) are checked when a pulse is applied and reported as structured errors. This implements the note's Rule 5.

**Flows** are the note's open question 5 made precise. A flow "move $S \to R$ at rate $\nu$ on $[a,b)$" is handled by **augmentation**: the model is extended with a transition $S \to R$ whose rate is a new parameter target with baseline $0$, and the flow becomes the parameter interval `set(rate, ν) during [a,b)`. Theorem (schedule level, Lean): the augmented program is conflict-free iff the original is, and its parameter narrative restricts to the original on the original targets. Modelling assumption (documented, not proved): a transition with rate $0$ does not change the vector field. For AlgebraicPetri the augmentation is a Petri-net morphism (an inclusion), so it composes with Section 2.7.

**Lowering** to `PresetTimeCallback` is unchanged in mechanism but is now *specified*: events are the sorted endpoints of spans plus the instants; at each event, targeted parameters are set to $\mathrm{fold}_j(P,t) \triangleright \theta_0$ and pulses are applied. Theorem (lowering correctness, Lean, on a pure model of the integrator): the piecewise-constant parameter trajectory produced by "hold the value from the last event" equals $P \triangleright \theta_0$ at every time, given a constant baseline. This is the algorithmic content of the callback and is exactly what the four v0.1 SIR vignettes tested by hand. The baseline cache (finding 5) is replaced by capturing the baseline in `initialize!` into the callback's own state per solve and clearing it on `finalize`.

Discrete models: pulses are applied **before** the update at step $t$ (the note's pre-update convention), stated in the docs and encoded in the lowering theorem for ℤ.

## Model morphisms and transport

A **target map** $f: T \to T'$ is any function; a **model morphism** $\phi: M \to M'$ induces one on targets. For AlgebraicPetri, an `ACSetTransformation` between Petri nets gives $f$ on species (states) and transitions (rates). Two operations:

- **Pushforward** $f_* P$: rename each atom's target along $f$. Functorial: $(g \circ f)_* = g_* \circ f_*$. Theorem: if $f$ is injective on the targets $P$ uses, then $f_*P$ is conflict-free iff $P$ is. If $f$ merges targets, new conflicts can appear, and the conflict report names the merged targets. This is the honest statement of "transport can fail".
- **Lift** along a projection $\pi: T' \to T$ with finite fibres (a stratified model projecting to its base): $\pi^* P$ places a copy of each atom on every $j'$ with $\pi(j') = j$. Functorial in $\pi$. Theorem: $\pi^*P$ is conflict-free iff $P$ is, and $(\pi^*P \triangleright \theta')(t)_{j'} = \mathrm{fold}_{\pi j'}(P,t) \triangleright \theta'(t)_{j'}$. Then age-specific refinements are ordinary composition: $\pi^*P \,\#\, Q$ where $Q$ touches only some strata.

With Catlab's typed-Petri-net stratification (a pullback of Petri nets over a type system), the projection to the base SIR net is a morphism, so `lift(program, projection)` is a one-liner for the user and a theorem for the researcher. This is the note's "transport along model morphisms" delivered.

## Temporal queries (from the paper)

Fix a finite window $t_0 < \dots < t_n$ of ℤ. Encode the zigzag category on this window as a Catlab schema (the paper's Listing 1, generalized to $n$ points), and encode $\mathcal{A}_P$ restricted to the window as an ACSet instance: parts at $[t_k]$ are the atoms active at $t_k$, parts at $[t_k, t_{k+1}]$ are the atoms active throughout, with the two restriction homs. Because Section 2.4 proves $\mathcal{A}_P$ is a presheaf on the zigzag, this instance is well-formed by construction.

Catlab then provides `subobject_classifier` and the Heyting operations, so the package can offer, with no new mathematics:

- `throughout(P, j, [t_k, t_{k+1}])` and `sometime(P, j, [t_k, t_{k+1}])`: the persistent and cumulative predicates for "target $j$ is under intervention";
- the paper's five truth values on a unit interval, reported in plain words ("in force at the start, lifted before the end");
- implication between programs: `P ⟹ Q` as a subobject, answering "wherever $P$ is in force, is $Q$?".

Scope statement for the docs: the queries operate on the *specification* $\mathcal{A}_P$, not on simulation output, and only on finite windows of a discrete grid. The topos structure is Catlab's; the package's contribution is the encoding and the proof that it is a valid presheaf. This is the review's Bridge 4.

## Inference: recovering a program from schedules

Given a baseline schedule $\theta_0$ and an observed or fitted schedule $\theta_1$, both piecewise constant, and an algebra on each target with a **division** (Multiplicative, Additive), `infer(θ0, θ1)` returns the unique minimal program $P$ of spans with $P \triangleright \theta_0 = \theta_1$: one atom per maximal run of constant ratio (or difference) on each target. Theorem (PutGet): $\mathrm{infer}(\theta_0, P \triangleright \theta_0) = P$ up to reordering and merging of adjacent equal atoms. This is the design note's lens `get`, restricted to the algebras where it is well defined, and it is useful: fitted time-varying $\beta(t)$ from a renewal model becomes a program that can be transported to another model.

# Julia architecture

## Module layout

```
src/
  CategoricalInterventions.jl   # exports, includes
  supports.jl                   # Span, Instant, membership, convexity helpers, epochs
  algebras.jl                   # PCM interface; Reject, Multiplicative, Additive, Cap, Floor, Affine; OrderedPolicy
  effects.jl                    # Set, Add, Scale, Transfer, Map; effect -> algebra element
  programs.jl                   # Atom, Program, active, fold, conflicts, compose (#), restrict
  narratives.jl                 # persistent(P), cumulative(P), evaluation on closed intervals
  semantics.jl                  # apply on schedules, sample (r^*), apply_discrete
  models.jl                     # Model, TargetSpace, invariants, declare!, augment (flows)
  transport.jl                  # pushforward, lift, functoriality checks
  lowering.jl                   # event schedule, pure lowering (no DiffEq dependency)
  infer.jl                      # infer(θ0, θ1)
  dsl.jl                        # @interventions, scale/add/set/transfer/flow, during/at
  show.jl                       # explain, tables, pretty printing
  unicode.jl                    # existing Unicode aliases, kept
ext/
  ...DiffEqCallbacksExt.jl      # to_callback, simulate
  ...AlgebraicPetriExt.jl       # Model from LabelledPetriNet; target maps from ACSetTransformation; augment
  ...StockFlowExt.jl
  ...AlgebraicDynamicsExt.jl
  ...ModelingToolkitExt.jl      # new: Model from ODESystem via parameter/unknown symbols
  ...CatlabQueriesExt.jl        # zigzag schema, encode window, throughout/sometime/⟹
  ...PlotsExt.jl                # plot(program): Gantt of supports by target
```

## The plain API

```julia
using CategoricalInterventions, AlgebraicPetri, OrdinaryDiffEq

model = Model(sir_petri)                      # rates :inf,:rec; states :S,:I,:R; algebras declared

program = @interventions model begin
    lockdown    = scale(:inf, 0.5)          during 5 .. 25
    vaccination = transfer(:S => :R, 50)    at 15
    campaign    = flow(:S => :R, rate=0.01) during 30 .. 60
end

explain(program)               # epoch table with plain-language rows
sol = simulate(model, program; u0, p0, tspan=(0.0, 60.0), saveat=0.5)
plot(program)                  # Gantt chart
```

`@interventions` is sugar over `Atom` constructors and `#`. Conflicts are reported at macro-expansion time when the model is a literal, otherwise at construction. The v0.1 names (`InterventionAtom`, `InterventionProgram`, `compose_interventions`, `to_callback`, `PetriIndexing`) remain as deprecated aliases for one minor version.

## The categorical API

```julia
A = persistent(program);  A[20.0, 30.0]      # atoms in force throughout [20, 30]
C = cumulative(program);  C[20.0, 30.0]      # atoms in force at some time in [20, 30]
epochs(program)                               # level sets of the active-atom map

P2 = pushforward(program, f)                  # f: target map or ACSetTransformation
P3 = lift(program, π)                         # π: projection of a stratified model
P4 = pushforward(program, augment(model, flows))

Pd = sample(program, grid)                    # r^* for a grid r(k) = t0 + kΔ
apply(program, θ0)                            # schedule -> schedule
infer(θ0, θ1; model)                          # schedule pair -> program

throughout(program, :inf, (20, 21)); sometime(program, :inf, (20, 21))
program ⟹ other                               # Heyting implication of active-atom subobjects
```

## Fixes to carry over from the review

| Finding | Fix |
|---|---|
| 1 conflict report duplicates atom | `fold` returns the offending pair; `Conflict` gains `required` |
| 2 `check=false` ignored | `epochs(P; check=false)` returns epochs with `fold = ⊥` marked, never throws |
| 3 algebra on `Target` | algebra lives on `Model`/`TargetSpace`; `Target` is name and kind only |
| 4 pulses need fake stop | `Instant` support type |
| 5 baseline cache leak | per-solve state in callback `initialize!`/`finalize!` |
| 6 `LatestWins` non-commutative | `OrderedPolicy` type, documented |
| 7 stringified ACSet | typed attributes; and the zigzag instance of Section 2.8 replaces it as the categorical representation |
| 8 `Any[]` | typed event vector, promoted element type |
| 9 README path | fixed |

# Lean proof programme

## Toolchain

Move to a current Lean 4 release with **Mathlib** as a dependency (`lake exe cache get` keeps builds to minutes). Mathlib supplies `LinearOrder`, `Set.OrdConnected` (convexity), `Finset`, `Monoid`, `MulAction`, and `Set.image/preimage` lemmas, which is most of what the proofs need. The current toolchain pin (4.11.0) must move to whatever the chosen Mathlib release requires.

## Modules and theorems

Each theorem name below is the name that appears in the docs ledger and in a Julia test of the same name.

**`Support.lean`** (generalizes the current `Interval.lean` from `Nat` to `[LinearOrder τ]`)

- `Span`, `Instant`, `Support`, `mem`
- `span_lo_mem`, `span_hi_not_mem`, `overlaps_symm`, `disjoint_of_hi_le_lo`
- `support_ordConnected : Set.OrdConnected (mem S)` (convexity)
- `inter_span : overlaps S S' → ∃ S'', mem S'' = mem S ∩ mem S'`

**`PCM.lean`**

- `class PCM (M)` with `one`, `mul : M → M → Option M`, `mul_comm`, `mul_assoc` (Kleisli form), `one_mul`
- `class PCMAction (M V)` with `act_one`, `act_mul`
- instances: `Reject`, `Multiplicative` (via any `CommMonoid` with `MulAction`), `Additive`, `Cap`, `Floor`, `Affine M`
- `affine_pcm`, `affine_action` (the two laws for `Affine`)
- `foldList : List M → Option M`; `fold_perm : l ~ l' → foldList l = foldList l'` (order irrelevance)
- `fold_pairwise_reject`, `fold_pairwise_total`, `fold_pairwise_affine` (pairwise suffices, per instance)

**`Program.lean`** (replaces `Composition.lean` and `Compatibility.lean`)

- `Atom`, `Program := List Atom`, `active`, `foldAt j P t`, `ConflictFree`
- `compose_assoc`, `compose_nil_left/right` (kept)
- `active_append : active (P ++ Q) t = active P t ++ active Q t`
- `conflictFree_append_left/right : ConflictFree (P ++ Q) → ConflictFree P ∧ ConflictFree Q`
- `conflictFree_of_pairwise` and `pairwise_of_conflictFree` (for shipped PCMs)
- `different_target_compatible`, `disjoint_compatible` (kept, now corollaries)

**`Epoch.lean`**

- `boundaries`, `epochs`, `epoch_cover : t ∈ ⋃ supports → ∃! e ∈ epochs P, t ∈ e`
- `active_const_on_epoch`
- `epochs_refine : e' ∈ epochs (P ++ Q) → ∃ e ∈ epochs P, e' ⊆ e` (functorial refinement)

**`Narrative.lean`**

- `persistent P I`, `cumulative P I` on closed intervals
- `persistent_antitone`, `cumulative_monotone`
- `persistent_glue : a ≤ p → p ≤ b → persistent P [a,b] = persistent P [a,p] ∩ persistent P [p,b]`
- `cumulative_union`, `cumulative_inter_eq_point` (uses `support_ordConnected`)
- `persistent_eq_active_of_point : persistent P [t,t] = active P t`

**`Semantics.lean`**

- `apply P θ` for `ConflictFree P`
- `apply_nil`, `apply_local`, `apply_append` (homomorphism, acting algebras), `apply_append_affine`, `apply_comm`
- `pullback r P`, `apply_pullback : (apply P θ) ∘ r = apply (pullback r P) (θ ∘ r)` (naturality)
- `grid_preimage_span` (the ceiling-endpoint formula), `apply_discrete_eq` (corollary)
- `apply_const_on_epoch`

**`Transport.lean`**

- `pushforward f P`, `lift π P`
- `pushforward_comp`, `lift_comp`
- `conflictFree_pushforward_of_injOn`, `conflictFree_lift_iff`
- `apply_lift`

**`Lowering.lean`**

- `events P`, `holdLast : (List (τ × V)) → τ → V`, `lower P θ0`
- `lower_eq_apply : ∀ t, holdLast (lower P θ0) t = apply P (const θ0) t` (callback correctness)
- `pulse_before_update` (discrete convention)
- `transfer_preserves_sum`

**`Augment.lean`**

- `augment`, `augment_conflictFree_iff`, `augment_restrict`

**`Infer.lean`** (last; needs division in the algebra)

- `infer`, `infer_putget`

Roughly 40 theorems replacing the current 9. The three existing files' results are preserved as special cases so nothing regresses.

## Correspondence and CI

- `docs/src/verified.md` is a table: claim in words, Lean theorem, Julia function, Julia test. Generated by a script that greps `theorem` names from the Lean sources and fails the docs build if a ledger entry has no matching theorem.
- CI runs `lake build` (with Mathlib cache) and the Julia tests. A Julia test file `test/laws.jl` checks each equational theorem on random programs (property-based, using a small generator of atoms), so the Lean statement and the Julia implementation are exercised on the same examples.
- The docs say, in one sentence: "Lean verifies the algebra of programs, their action on schedules, and the lowering algorithm; it does not verify the ODE solver or Catlab."

# Documentation plan

Target: a reader who wants to add a lockdown to an SIR model is productive in five minutes without meeting a sheaf; a reader who wants the mathematics finds every claim with its proof.

```
docs/src/
  index.md          Three paragraphs: what it does, the one-sentence honesty statement, where to go next.
  quickstart.md     The plain API on an SIR model: model, @interventions, explain, simulate, plot. One page.
  concepts.md       Targets, supports, effects, conflicts, epochs, in plain language with one figure. One page.
  howto/
    algebraicpetri.md   stockflow.md   algebraicdynamics.md   modelingtoolkit.md   discrete.md
    flows.md            transport.md   queries.md             infer.md
  semantics.md      The precise statement: what a program means as a function of time; what the callback guarantees;
                    the pulse-before-update convention. One page, no category theory.
  categorical.md    For researchers: Sections 2.2 to 2.9 of this plan, condensed, each definition linked to Lean.
  verified.md       The generated ledger.
  api.md            Exported symbols, grouped as above.
```

Style rules: one idea per sentence; every page opens with what the reader will be able to do; code blocks are runnable and doctested (`doctest=true`, which v0.1 disables); no Unicode-only examples on user-facing pages (Unicode remains available and has its own page); every categorical page ends with a "what this buys you" paragraph.

# Vignette plan

Vignettes 04 to 07 (four copies of the same SIR story) are replaced. Each new vignette is written to demonstrate one structural idea and to run in under a minute.

| # | Title | Demonstrates | Structural idea |
|---|---|---|---|
| 01 | Getting started | plain DSL, SIR, lockdown + vaccination, `explain`, `plot` | atoms, programs, epochs |
| 02 | Composition and conflicts | `#`, conflict reports with `required`, `Affine` set-then-scale, `Cap` | PCMs as the composition law |
| 03 | One program, many models | the same program on AlgebraicPetri, StockFlow, AlgebraicDynamics, ModelingToolkit, and `FunctionMap`, with cross-checks; the sampling theorem shown numerically | naturality (Theorem 4) |
| 04 | Define once, stratify for free | lockdown on SIR; age-stratified SIR by typed-Petri-net pullback; `lift` along the projection; then compose a school-only closure; then merge two strata and watch a conflict appear | transport, functoriality, failure of transport |
| 05 | Pulses and flows | vaccination as a pulse versus a campaign as a flow; augmentation shown as a Petri-net morphism; conservation invariant checked | flows by augmentation, Rule 5 |
| 06 | Narratives and queries | `persistent` and `cumulative` on a policy timeline; zigzag ACSet window; the five truth values in words; `P ⟹ Q` for "masking only where lockdown" | sheaf/cosheaf, internal logic |
| 07 | Recovering interventions from data | fit a piecewise $\beta(t)$ (or take one from the literature), `infer` a program, transport it to a different model | lens `get`, PutGet |
| 08 | Individual-level (stretch) | a temporal contact graph as a `Grph`-narrative in Catlab; lockdown as a subobject; a temporal-path check before and after | the paper's Section 3.1 with interventions |

Vignettes 01 to 03 of v0.1 are folded into the new 01 and 02. Each vignette ends with a short "what the category theory bought" paragraph that points at the theorem used.

# Milestones

| Milestone | Content | Acceptance |
|---|---|---|
| **M0 Honesty and fixes** | findings 1 to 9; README rewritten to describe v0.1 accurately; `Instant`; algebra on model | tests for every finding; docs no longer overclaim |
| **M1 Algebraic core** | PCMs, `Affine`, `OrderedPolicy`, `fold`, conflict reports, epochs, `apply`, `sample` | Lean `Support`, `PCM`, `Program`, `Epoch`, `Semantics`; property tests |
| **M2 Models and lowering** | `Model` from AlgebraicPetri/StockFlow/AlgebraicDynamics/MTK; `simulate`; invariants; transfers; new callback state handling | Lean `Lowering`; vignette 03 passes with cross-checks |
| **M3 Transport and flows** | `pushforward`, `lift`, `augment`; typed-Petri stratification example | Lean `Transport`, `Augment`; vignettes 04, 05 |
| **M4 Narratives and queries** | `persistent`, `cumulative`, zigzag window, `throughout`/`sometime`/`⟹` | Lean `Narrative`; vignette 06 |
| **M5 Inference** | `infer` for Multiplicative and Additive | Lean `Infer`; vignette 07 |
| **M6 Docs and release** | full docs per Section 5; ledger generator in CI; v0.2.0 | doctests pass; ledger complete; no `sorry` |

Estimated effort at a steady pace: M0 one week; M1 and M2 three weeks each; M3 two weeks; M4 two weeks; M5 one week; M6 two weeks. Vignette 08 is outside the estimate.

# Claims ledger

What the v0.2 documentation will say, and what backs each statement.

| Claim (docs wording) | Definition | Lean | Test |
|---|---|---|---|
| Programs compose associatively with an empty identity | `#` | `compose_assoc`, `compose_nil_*` | `laws.jl` |
| Under a commutative algebra, composition order does not matter | PCM | `fold_perm`, `apply_comm` | `laws.jl` |
| A program is conflict-free iff every pair of overlapping same-target atoms combines | `conflicts` | `conflictFree_of_pairwise` | `laws.jl` |
| Set-then-scale is well defined; two sets on one target are a conflict | `Affine` | `affine_pcm`, `fold_affine_isSome_iff` | `core.jl` |
| Under set-then-scale the absolute value applies first regardless of order | `Affine` | `affine_action`, `affine_act_mul_of_relative` | `laws.jl` |
| A program is a persistent narrative (sheaf) of atoms in force throughout an interval | `persistent` | `persistent_glue` | `narratives.jl` |
| A program is a cumulative narrative (cosheaf) of atoms in force at some time in an interval | `cumulative` | `cumulative_inter_eq_point` | `narratives.jl` |
| Adding atoms only refines epochs | `epochs` | `epochs_refine` | `laws.jl` |
| Applying a program commutes with restricting or resampling the schedule | `apply`, `sample` | `apply_pullback` | vignette 03 |
| The same program is correct on continuous and grid models | `sample` | `apply_discrete_eq` | vignette 03 |
| The callback produces exactly the epoch-table schedule | `lower` | `lower_eq_apply` | `lowering.jl` |
| Transfers conserve population | `Transfer` | `transfer_preserves_sum` | `models.jl` |
| Transport along an injective model morphism preserves conflict-freeness; merging targets can create conflicts | `pushforward` | `conflictFree_pushforward_of_injOn` | vignette 04 |
| Lifting to a stratified model preserves conflict-freeness and acts stratum-wise | `lift` | `conflictFree_lift_iff`, `apply_lift` | vignette 04 |
| A flow is a parameter intervention on the augmented model | `augment` | `augment_restrict` | vignette 05 |
| Inferring a program from a program's own output returns the program | `infer` | `infer_putget` | `infer.jl` |

Statements deliberately **not** claimed: that the sheaf topos structure is formalized (only the two gluing equations are); that $r^*$ is a geometric morphism (cited to the paper, not proved here); anything about ODE solution accuracy; a categorical treatment of uncertain effects (effects are generic over value types, so `Measurements.jl` values work by duck typing, and the docs say only that).

# Risks and non-goals

- **Mathlib build time and version churn.** Mitigated by the cache and by pinning; the proofs use only stable, elementary parts of Mathlib.
- **Catlab API churn** (0.16 to 0.17 already differs). The zigzag encoding and `subobject_classifier` are the only Catlab-heavy parts; they live in an extension so the core never breaks.
- **Scope creep toward a general hybrid-systems library.** Flows are handled by augmentation only; arbitrary vector-field edits (the note's "vector-field interval") are a non-goal for v0.2.
- **Individual-level models.** Vignette 08 shows the idea on the paper's temporal graphs but no ABM integration is promised.
- **Uncertainty and provenance.** Metadata carries provenance and priority; only `OrderedPolicy` reads it. Probabilistic effects are out of scope.

# Implementation notes (v0.2.0, 2026-09-19)

Deviations from the plan above, recorded so the documentation never claims
more than was built.

- **`Affine` is a PCM but not a monoid action.** The action law
  `act(a·b) = act a ∘ act b` is false when one factor is absolute. The law
  that holds, and is proved (`affine_action`), is "absolute first, then the
  product of the relative parts". Consequently the sequential homomorphism
  `(P ⊕ Q) ▷ θ = Q ▷ (P ▷ θ)` holds under `Affine` only when `Q` is purely
  relative (`apply_append_affine`); the order-independence theorem
  (`apply_comm`) holds for every PCM. Section 2.2 and 2.5 should be read with
  this correction.
- **Stratification uses untyped pullbacks.** AlgebraicPetri 0.10's
  `typed_product` fails under Catlab 0.17 (attribute components of typed
  nets). `stratify(base, strata, types, base_types, strata_types)` types the
  untyped copies of the nets positionally, takes the pullback with
  `pullback[ACSetCategory(...)]`, relabels with tuple names, and returns a
  lightweight `PetriMorphism` for each projection. `lift` and `pushforward`
  accept these and genuine `ACSetTransformation`s.
- **Queries use a graph over the path graph**, not a generated zigzag
  schema: by Niu et al. Corollary 2.7 the two are equivalent, and Catlab's
  `Graph` subobjects are well supported. Heyting operations dispatch through
  `ACSetCategory`.
- **ModelingToolkit extension** builds a model from a completed system with
  symbolic parameter selectors (SymbolicIndexingInterface `getp`/`setp`) and
  positional states; verified against ModelingToolkit 11.26.8 in a separate
  environment, since the package test environment does not include it. Flows
  are not supported there.
- **`augment` beyond Petri nets** wraps function-valued dynamics (StockFlow
  vector fields, hand-written ODEs, discrete maps) and converts
  AlgebraicDynamics systems to functions; only Petri nets get a structural
  transition. Vignette 08 was not built. `infer` merges runs in Julia; the Lean `infer` is the one-atom-
  per-cell version, proved at every grid point including the last
  (`infer_putget_grid_step`).
- **Lean hypotheses.** `conflictFree_lift_iff'` needs the projection to be
  surjective onto the targets the program uses (the Julia precondition); `lift_comp` is functoriality at the level of
  folds (the lifted lists are permutations of each other); pairwise-suffices is
  proved per instance (`Reject`, every total PCM, `Affine` over a total PCM).
- **Discrete pulses** are applied before the step, as planned; this is stated
  in the docs and formalised as the definition `discreteStep`.
