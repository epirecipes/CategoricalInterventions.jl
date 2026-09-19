# [The categorical view](@id categorical)

```@meta
CurrentModule = CategoricalInterventions
```

This page is for readers who want the structure. Every definition names the
Lean theorem that backs it; the [verified properties](@ref verified) page has
the full table.

## Time and supports

The timeline is any linear order. Supports are spans `[lo, hi)` and instants;
both are order-convex (`support_ordConnected`), and convexity is the only
property the theory uses.

## Effect algebras are partial commutative monoids

Each target carries a PCM: a unit, a commutative and associative partial
product, and an action on values. `Reject`, `Multiplicative`, `Additive`,
`Cap`, `Floor` are instances; for all of them the product of a list is defined
iff every pair is defined (`foldList_isSome_iff_pairwise`), which is what
makes the pairwise conflict check complete
(`conflictFree_of_pairwise`). `Affine(M)` is a PCM (`affine_pcm`) whose
elements are an optional absolute value and a relative effect; its action
applies the absolute value first and the relative product second
(`affine_action`). It is not a monoid action, which is why sequential
application under `Affine` is only a homomorphism when the later program is
purely relative (`apply_append_affine`). Ordered policies are not PCMs and are
kept in a separate type.

## Programs are narratives

For a closed interval $I$, let $\mathcal{A}_P(I)$ be the atoms whose support
contains $I$ and $\mathcal{C}_P(I)$ the atoms whose support meets $I$. Then for
$a \le p \le b$

```math
\mathcal{A}_P[a,b] = \mathcal{A}_P[a,p] \cap \mathcal{A}_P[p,b], \qquad
\mathcal{C}_P[a,b] = \mathcal{C}_P[a,p] \cup \mathcal{C}_P[p,b], \quad
\mathcal{C}_P[a,p] \cap \mathcal{C}_P[p,b] = \mathcal{C}_P[p,p].
```

These are the sheaf and cosheaf conditions for the Johnstone coverage of the
interval site of Bumpus et al. and Niu et al. (`persistent_glue`,
`cumulative_union`, `cumulative_inter_eq_point`). No Grothendieck topology is
formalised; the equations are. Epochs are the level sets of the active-atom map
(`active_const_on_epoch`), and adding atoms refines them (`epochs_refine`).

## Application is a natural transformation

The schedule sheaf sends an interval to the functions on it. A conflict-free
program acts pointwise, so application commutes with restriction along any map
of timelines (`apply_pullback`); grid sampling is the case of an affine map
from the integers (`grid_preimage_span`, `apply_discrete_eq`). This is the
theorem behind "one program, many models".

## Transport

A map of targets $f$ pushes programs forward (`pushforward`, functorial by
`pushforward_comp`); it preserves conflict-freeness when injective on the
targets used (`conflictFree_pushforward_of_injOn`) and may create conflicts
when it merges targets. A projection $\pi$ from a stratified target space lifts
programs by copying each atom onto every fibre element (`lift`,
`lift_comp`); lifting preserves conflict-freeness (`conflictFree_lift_iff`)
and acts stratum-wise (`apply_lift`). For AlgebraicPetri, [`stratify`](@ref)
computes the pullback of typed nets and returns the projections, so a lockdown
defined once on SIR lifts to an age-stratified SIR in one call.

## Queries in the subobject lattice

On a finite window of a discrete grid, the target-level persistent narrative is
a graph over the path graph (Niu et al., Corollary 2.7): a vertex per
target and time, an edge per target and unit interval that the target is
covered throughout. Catlab's subobject lattice then supplies meet, join,
negation and Heyting implication, and the five truth values of the paper's
subobject classifier on a unit interval are read off a pair of vertices and an
edge ([`truth_value`](@ref)). The queries act on the specification, not on
simulation output.

## Inference is a lens `get`

For a multiplicative or additive algebra, [`infer`](@ref) recovers a program
from a baseline and an observed schedule, one atom per maximal run of constant
ratio or difference; applying it to the baseline returns the observed
schedule (`infer_putget`).
