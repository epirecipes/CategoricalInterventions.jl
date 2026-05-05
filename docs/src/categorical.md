# [Categorical structures](@id categorical-structures)

```@meta
CurrentModule = CategoricalInterventions
```

The package uses Catlab.jl for lightweight categorical views of intervention
programs and time refinements.

## Epochs as a time partition

[`epochize`](@ref) refines all intervention supports into a common partition of
active intervals. Each [`Epoch`](@ref) records:

- the half-open support interval;
- the atoms active on that interval;
- the combined effects for each full target identity.

This refinement is useful when comparing sampled time points, discrete
schedules, and model intervals.

## FinFunctions from time samples to epochs

[`epoch_finfunction`](@ref) maps sampled time points to the epoch containing each
time:

```julia
epochs = epochize(program)
f = epoch_finfunction([10.0, 15.0, 25.0], epochs)
```

The result is a Catlab `FinFunction` from sampled times to epoch indices.

## ACSets for intervention programs

[`as_acset`](@ref) encodes an intervention program as
[`InterventionProgramData`](@ref), a Catlab ACSet with parts for atoms and target
objects plus attributes for identifiers, target names, kinds, supports, effect
modes, and effect values.

```julia
data = as_acset(program)
```

This representation is intended for inspection, categorical bookkeeping, and
future integrations with richer Catlab workflows.

## Relationship to application APIs

The internal epoch representation keys effects by [`Target`](@ref), so distinct
kinds with the same name remain separate. The scalar and discrete application
APIs, [`apply_interventions`](@ref) and [`apply_discrete`](@ref), intentionally
use symbol-keyed dictionaries for ergonomic baseline data. Those application
APIs require names to be unambiguous across target kinds.
