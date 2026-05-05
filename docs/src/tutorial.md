# [Tutorial](@id tutorial)

```@meta
CurrentModule = CategoricalInterventions
```

This tutorial covers the core data model: targets, intervals, effects,
programs, conflicts, epoch refinement, and schedule application.

## Targets and intervals

A [`Target`](@ref) names the model component affected by an intervention. The
target kind determines how the intervention is interpreted later:

```julia
using CategoricalInterventions

beta = Target(:beta; kind=Parameter, value_type=Float64)
infectious = Target(:I; kind=State, value_type=Float64)
```

Intervals are half-open: `[start, stop)`. The start time is included and the
stop time is excluded.

```julia
school_term = Interval(10.0, 30.0)
```

## Effects and intervention atoms

Effects describe the local edit. The built-in effects are:

- [`SetValue`](@ref): replace the current value;
- [`Add`](@ref): add a delta;
- [`Scale`](@ref): multiply by a factor;
- [`MapEffect`](@ref): call a custom mapping function.

An [`InterventionAtom`](@ref) combines an identifier, target, support interval,
and effect:

```julia
closure = InterventionAtom(:school_closure, beta, Interval(10.0, 30.0), Scale(0.6))
```

`Target.value_type` is enforced for absolute assignments and for the result of
effect application. For example, a `Target` declared with `value_type=Float64`
will reject a `SetValue("closed")` atom.

## Programs and conflicts

An [`InterventionProgram`](@ref) is a finite list of atoms:

```julia
program = InterventionProgram(closure)
```

Different targets can overlap. Same-target overlaps require an explicit
combination algebra; otherwise they are conflicts.

```julia
beta_mult = Target(:beta; kind=Parameter, value_type=Float64,
                   algebra=MultiplicativeAlgebra())

closure = InterventionAtom(:closure, beta_mult, Interval(10.0, 30.0), Scale(0.6))
masking = InterventionAtom(:masking, beta_mult, Interval(20.0, 40.0), Scale(0.8))

combined = compose_interventions(InterventionProgram(closure),
                                 InterventionProgram(masking))
```

The overlap `[20, 30)` scales by `0.6 * 0.8`.

Use [`conflicts`](@ref) to inspect unresolved overlaps and [`validate`](@ref) to
return a Boolean:

```julia
conflicts(combined)
validate(combined)
```

## Epoch refinement

[`epochize`](@ref) computes the common interval refinement induced by all
intervention endpoints. Each epoch stores active atoms and their combined
effects keyed by full [`Target`](@ref) identity, not just by name:

```julia
epochs = epochize(combined)
[(epoch.support, collect(keys(epoch.effects))) for epoch in epochs]
```

Target identity includes both `name` and `kind`, so a parameter named `:x` and a
state named `:x` can be represented in the same program without internal
collisions.

## Applying to baselines

For scalar baselines, use [`apply_interventions`](@ref):

```julia
values = apply_interventions(combined, Dict(:beta => 0.30))
```

The scalar application API is dictionary-based and keyed by symbol, so it
requires target names to be unambiguous across target kinds.

For vector-valued discrete schedules, use [`apply_discrete`](@ref):

```julia
times = collect(0:5)
baseline = Dict(:beta => fill(0.30, length(times)))
schedule = apply_discrete(combined, baseline, times)
```

Immutable schedule inputs, such as ranges, are materialized into mutable output
vectors before interventions are applied.
