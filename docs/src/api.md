# [API reference](@id api-reference)

```@meta
CurrentModule = CategoricalInterventions
```

## Supports

```@docs
Span
Instant
..
Interval
contains_time
overlaps
intersection
endpoints
```

## Effects

```@docs
Identity
SetValue
Add
Scale
CapAt
FloorAt
MapEffect
AffineEffect
Transfer
Flow
apply_effect
```

## Algebras

```@docs
Reject
Multiplicative
Additive
Cap
Floor
Affine
LatestWins
HighestPriority
combine
```

## Targets, atoms, programs

```@docs
TargetKind
Parameter
State
Process
Observation
Target
TargetSpec
TargetSpace
declare!
algebra
value_type
Atom
InterventionAtom
Program
expand
active
Conflict
InterventionConflictError
conflicts
validate
compose
restrict
shift
extent
seq
⋙
Epoch
epochs
active_effects
boundaries
```

## Narratives

```@docs
persistent
cumulative
```

## Semantics

```@docs
apply
EpochValues
sample
```

## Models

```@docs
Model
Indexing
Conserved
Nonnegative
InvariantViolation
program
parameters
states
targets
check_targets
augment
augment_flow
extend_parameters
target_map
strata
stratify
typed_by
dom
codom
conserves_tokens
```

## Lowering and simulation

```@docs
event_times
active_parameter_effects
state_pulses_at
apply_parameter_effects!
apply_state_pulses!
apply_to_integrator!
lower
hold_last
to_callback
simulate
```

## Transport

```@docs
pushforward
lift
lift_along
fibres
```

## Plain constructors

```@docs
scale
set
add
cap
floor_at
custom
transfer
flow
@interventions
```

## Display

```@docs
explain
table
plot_program
```

## Inference

```@docs
infer
```

## Queries

```@docs
NarrativeWindow
NarrativeSubobject
subobject
at
throughout
sometime
truth_value
describe
```

## Deprecated aliases

`InterventionProgram`, `compose_interventions`, `epochize`,
`apply_interventions`, `apply_discrete`, `PetriIndexing`, and
`callback_times` are the v0.1 names of `Program`, `compose`, `epochs`,
`apply`, `apply`, `Indexing`, and `event_times`.
