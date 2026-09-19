"""
CategoricalInterventions.jl: composable, time-varying interventions for
epidemiological models.

Interventions are typed local edits to a model over spans and instants. They
compose when compatible, conflict otherwise, normalise to epochs, act on
schedules, lower to solver callbacks, and transport along model morphisms. The
algebraic core is specified in `design/PLAN.md` and verified in `proofs/`.
"""
module CategoricalInterventions

using Catlab

# supports
export Span, Instant, Interval, .., contains_time, overlaps, intersection, endpoints
# effects and algebras
export Identity, SetValue, Add, Scale, CapAt, FloorAt, MapEffect, AffineEffect, Transfer, Flow, apply_effect
export Reject, Multiplicative, Additive, Cap, Floor, Affine, LatestWins, HighestPriority, combine
# targets, atoms, programs
export TargetKind, Parameter, State, Process, Observation
export Target, TargetSpec, TargetSpace, declare!, algebra, value_type
export Atom, InterventionAtom, Program, InterventionProgram, expand, active
export Conflict, InterventionConflictError, conflicts, validate
export compose, compose_interventions, ⊕, restrict, Epoch, epochs, epochize, active_effects, boundaries
# narratives
export persistent, cumulative
# semantics
export apply, apply_interventions, apply_discrete, EpochValues, sample, ⊙
# models
export Model, Indexing, PetriIndexing, Conserved, Nonnegative, InvariantViolation
export program, parameters, states, targets, check_targets, augment, augment_flow, extend_parameters
export target_map, strata, conserves_tokens, stratify, typed_by, dom, codom
# lowering
export event_times, callback_times, active_parameter_effects, state_pulses_at
export apply_parameter_effects!, apply_state_pulses!, apply_to_integrator!, lower, hold_last
export to_callback, simulate
# transport
export pushforward, lift, fibres
# dsl
export scale, set, add, cap, floor_at, custom, transfer, flow, @interventions
# show
export explain, table, plot_program
# unicode
export ℙ, 𝕊, 𝕀, ι, Π, ≜, δ, κ
# inference
export infer
# queries
export NarrativeWindow, NarrativeSubobject, subobject, at, throughout, sometime, truth_value, describe
export meet, join, implies, negate, ∧, ∨, ⟹, ¬

include("supports.jl")
include("algebras.jl")
include("programs.jl")
include("narratives.jl")
include("semantics.jl")
include("models.jl")
include("lowering.jl")
include("transport.jl")
include("dsl.jl")
include("show.jl")
include("unicode.jl")
include("infer.jl")
include("queries.jl")

end # module
