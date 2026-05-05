# [Callback lowering](@id callback-lowering)

```@meta
CurrentModule = CategoricalInterventions
```

`CategoricalInterventions.jl` can lower an [`InterventionProgram`](@ref) to a
`DiffEqCallbacks.PresetTimeCallback` via [`to_callback`](@ref). This is intended
for SciML integrators whose state values live in `integrator.u` and whose rates
or parameters live in `integrator.p`, including ODE problems generated from
AlgebraicPetri.jl models.

Load `DiffEqCallbacks` before calling [`to_callback`](@ref):

```julia
using CategoricalInterventions
using DiffEqCallbacks
```

## Indexing

[`PetriIndexing`](@ref) maps target names to selectors for `integrator.p` and
`integrator.u`.

For labelled containers such as `LabelledArrays.LVector`, pass vectors of names:

```julia
indexing = PetriIndexing(parameters=[:inf, :rec],
                         states=[:S, :I, :R])
```

For plain vectors, pass dictionaries:

```julia
indexing = PetriIndexing(parameters=Dict(:inf => 1, :rec => 2),
                         states=Dict(:S => 1, :I => 2, :R => 3))
```

Labelled and positional selectors can be mixed between parameters and states:

```julia
indexing = PetriIndexing(parameters=[:inf, :rec],
                         states=Dict(:S => 1, :I => 2, :R => 3))
```

## Parameter intervals

Targets with kind [`Parameter`](@ref), [`Process`](@ref), or
[`Observation`](@ref) are treated as parameter-like interval effects. The
callback fires at interval start and stop times.

At each parameter event, only selectors targeted by the intervention program are
reset to baseline before active effects are applied. Untargeted entries in
`integrator.p` are left unchanged, which allows independent callbacks or solver
logic to update unrelated parameters.

If `baseline_p` is provided, that vector is used as the parameter baseline:

```julia
cb = to_callback(program, indexing; baseline_p=p0)
```

If `baseline_p` is omitted, each solve captures its own baseline from the
integrator. Reusing the same callback object across solves is therefore safe for
different initial parameter vectors.

Intervals active at the initial solve time are applied during callback
initialization, so an interval like `Interval(-5.0, 10.0)` is active when
`tspan` starts at `0.0`.

## State pulses

Targets with kind [`State`](@ref) are treated as instantaneous pulses at
`support.start`. The support stop time is retained in the atom but does not
create a callback event for state targets.

A vaccination transfer from susceptible to recovered can be written as paired
state pulses:

```julia
susceptible = Target(:S; kind=State, value_type=Float64,
                     algebra=AdditiveAlgebra())
recovered = Target(:R; kind=State, value_type=Float64,
                   algebra=AdditiveAlgebra())

vaccination = InterventionProgram(
    InterventionAtom(:vaccinate_from_s, susceptible, Interval(15.0, 16.0), Add(-50.0)),
    InterventionAtom(:vaccinate_to_r, recovered, Interval(15.0, 16.0), Add(50.0)),
)
```

## AlgebraicPetri-style SIR sketch

For an SIR model with rates `:inf` and `:rec` and states `:S`, `:I`, and `:R`:

```julia
inf_rate = Target(:inf; kind=Parameter, value_type=Float64,
                  algebra=MultiplicativeAlgebra())

lockdown = InterventionProgram(
    InterventionAtom(:lockdown, inf_rate, Interval(5.0, 25.0), Scale(0.5)),
)

indexing = PetriIndexing(parameters=[:inf, :rec],
                         states=[:S, :I, :R])

cb = to_callback(lockdown, indexing; baseline_p=p0)
```

Pass `cb` to `solve` using the usual SciML callback keyword.
