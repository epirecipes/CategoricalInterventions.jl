# [Concepts](@id concepts)

```@meta
CurrentModule = CategoricalInterventions
```

Five words cover the whole package.

**Target.** What an intervention changes: a named rate or parameter, or a
named state. A target is identified by its name and kind. Its value type and
its combination algebra are declared once, on the model or on a
[`TargetSpace`](@ref), never on the intervention.

**Support.** When the intervention is in force. A [`Span`](@ref) `lo .. hi` is
half-open: in force at `lo`, lifted at `hi`, so adjacent spans do not overlap.
An [`Instant`](@ref) is a single time. Parameter interventions live on spans;
state pulses live on instants; state flows live on spans.

**Effect.** What happens to the value: [`Scale`](@ref), [`Add`](@ref),
[`SetValue`](@ref), [`CapAt`](@ref), [`FloorAt`](@ref), a custom
[`MapEffect`](@ref); for states also [`Transfer`](@ref) (move people between two
states in one atom) and [`Flow`](@ref) (a continuous transfer at a rate).

**Algebra.** What two effects on the same target at the same time mean
together. The defaults are the useful ones: rates use `Affine(Multiplicative())`,
"set at most once, then scale as often as you like"; states use `Additive()`.
Any target without a declaration uses `Reject()`, where overlaps are conflicts.
`Cap()` and `Floor()` take the tighter bound. All of these are partial
commutative monoids, so the order in which you write atoms never matters.
`LatestWins()` and `HighestPriority()` are different: they resolve overlaps by
order or by a priority in the atom's metadata, and are kept in a separate class
so that order-dependence is visible in the type.

**Program.** A list of atoms with the declaration table of their targets.
Programs compose with [`compose`](@ref) or `⊕`. Composition is associative with
the empty program as identity. Different targets never conflict; the same
target on disjoint supports never conflicts; the same target on overlapping
supports conflicts unless the algebra combines the effects. A conflict report
names the target, the overlap, both atoms, and an algebra that would resolve
it.

```jldoctest concepts
julia> using CategoricalInterventions

julia> p = Program([set(:beta, 0.1; during=0..10, id=:a), set(:beta, 0.2; during=5..15, id=:b)]);

julia> conflicts(p)
1-element Vector{Conflict}:
 Conflict(Parameter:beta on [5, 10): a vs b; effects set(0.1) and set(0.2) do not combine under Reject(); declare LatestWins())
```

## Epochs

The endpoints of all spans cut time into **epochs**, on each of which the set
of active atoms is constant. [`epochs`](@ref) returns them with the combined
effect per target; [`explain`](@ref) prints them in words. Adding atoms only
refines the partition.

## Two narratives

A program can be read in two ways over a closed window `[a, b]`:
[`persistent`](@ref) gives the atoms in force *throughout* the window,
[`cumulative`](@ref) the atoms in force *at some time* in it. These are the
sheaf and cosheaf of the paper by Niu, Osgood, Zelko and Srinivasan, and the
[categorical view](@ref categorical) says what that buys.

## Models

A [`Model`](@ref) wraps a dynamics object from your framework with the
declared targets, the selectors that locate each target in the integrator's
`p` and `u`, and the invariants pulses must preserve ([`Conserved`](@ref),
[`Nonnegative`](@ref)). Extensions build models from AlgebraicPetri nets,
StockFlow diagrams, AlgebraicDynamics systems and ModelingToolkit systems; [`simulate`](@ref) solves
them with a program attached.
