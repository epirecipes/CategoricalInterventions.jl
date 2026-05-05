# [API reference](@id api-reference)

```@meta
CurrentModule = CategoricalInterventions
```

## Target kinds

```@docs
Parameter
State
Process
Observation
```

## Core data types

```@docs
Interval
Target
InterventionAtom
InterventionProgram
Conflict
InterventionConflictError
Epoch
EpochValues
```

## Effects

```@docs
SetValue
Add
Scale
MapEffect
apply_effect
```

## Combination algebras

```@docs
RejectOverlap
AdditiveAlgebra
MultiplicativeAlgebra
LatestWins
```

## Program validation and composition

```@docs
conflicts
validate
compose_interventions
epochize
```

## Applying interventions

```@docs
apply_interventions
apply_discrete
```

## Callback lowering

```@docs
PetriIndexing
callback_times
active_parameter_effects
state_pulses_at
apply_parameter_effects!
apply_state_pulses!
apply_to_integrator!
to_callback
```

## Catlab representations

```@docs
epoch_finfunction
as_acset
InterventionProgramData
```

## Unicode shorthand

Unicode constructors and operators are documented on
[Unicode syntax](@ref unicode-syntax).
