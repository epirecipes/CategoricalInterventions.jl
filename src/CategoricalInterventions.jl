module CategoricalInterventions

using Dates
using Catlab
using Catlab: @present, @acset_type, FreeSchema, FinSet, FinFunction
using Catlab: add_parts!, set_subpart!

export Parameter, State, Process, Observation
export Interval, Target, InterventionAtom, InterventionProgram
export SetValue, Add, Scale, MapEffect, apply_effect
export RejectOverlap, AdditiveAlgebra, MultiplicativeAlgebra, LatestWins
export Conflict, InterventionConflictError, conflicts, validate, compose_interventions
export Epoch, EpochValues, epochize, apply_interventions, apply_discrete
export epoch_finfunction, as_acset, InterventionProgramData
export PetriIndexing, callback_times, active_parameter_effects, state_pulses_at
export apply_parameter_effects!, apply_state_pulses!, apply_to_integrator!, to_callback
export ℙ, 𝕊, 𝕀, ι, Π, ≜, δ, κ, ⊕, ⊙

@enum TargetKind Parameter State Process Observation

@doc """
    Parameter

Target kind for model parameters or rates stored in a SciML integrator's
parameter container.
""" Parameter

@doc """
    State

Target kind for state variables stored in a SciML integrator's state container.
State interventions lower to instantaneous pulses at the interval start.
""" State

@doc """
    Process

Target kind for process-level quantities. These are treated as parameter-like
targets by callback lowering.
""" Process

@doc """
    Observation

Target kind for observation-level quantities. These are treated as
parameter-like targets by callback lowering.
""" Observation

abstract type AbstractEffect end
abstract type AbstractCombinationAlgebra end

"""
    Interval(start, stop)

Half-open interval `[start, stop)`. Intervals are the support of interventions
and must satisfy `start < stop`.
"""
struct Interval{T}
    start::T
    stop::T

    function Interval{T}(start::T, stop::T) where {T}
        start < stop || throw(ArgumentError("Intervals must satisfy start < stop; got [$start, $stop)"))
        new{T}(start, stop)
    end
end

Interval(start::T, stop::T) where {T} = Interval{T}(start, stop)
function Interval(start, stop)
    promoted = promote(start, stop)
    return Interval(promoted...)
end

Base.show(io::IO, I::Interval) = print(io, "[$(I.start), $(I.stop))")

contains_time(I::Interval, t) = I.start <= t < I.stop
overlaps(a::Interval, b::Interval) = a.start < b.stop && b.start < a.stop
isdisjoint(a::Interval, b::Interval) = !overlaps(a, b)

function intersection(a::Interval, b::Interval)
    overlaps(a, b) || return nothing
    return Interval(max(a.start, b.start), min(a.stop, b.stop))
end

"""
    SetValue(value)

Absolute intervention effect: replace the target value with `value`.
"""
struct SetValue{T} <: AbstractEffect
    value::T
end

"""
    Add(delta)

Additive intervention effect: transform `x` to `x + delta`.
"""
struct Add{T} <: AbstractEffect
    delta::T
end

"""
    Scale(factor)

Multiplicative intervention effect: transform `x` to `x * factor`.
"""
struct Scale{T} <: AbstractEffect
    factor::T
end

"""
    MapEffect(f, label=:custom)

Custom intervention effect represented by an explicit map.
"""
struct MapEffect{F} <: AbstractEffect
    f::F
    label::Symbol
end

MapEffect(f) = MapEffect(f, :custom)

effect_mode(::SetValue) = :absolute
effect_mode(::Add) = :additive
effect_mode(::Scale) = :multiplicative
effect_mode(e::MapEffect) = e.label

"""
    apply_effect(effect, value)

Apply a local intervention effect to a value. `SetValue` replaces the value,
`Add` adds a delta, `Scale` multiplies by a factor, and `MapEffect` calls the
stored function.
"""
apply_effect(e::SetValue, value) = e.value
apply_effect(e::Add, value) = value + e.delta
apply_effect(e::Scale, value) = value * e.factor
apply_effect(e::MapEffect, value) = e.f(value)

Base.show(io::IO, e::SetValue) = print(io, "set($(e.value))")
Base.show(io::IO, e::Add) = print(io, "add($(e.delta))")
Base.show(io::IO, e::Scale) = print(io, "scale($(e.factor))")
Base.show(io::IO, e::MapEffect) = print(io, "map($(e.label))")

"""
    RejectOverlap()

Default algebra: overlapping effects on the same target are conflicts.
"""
struct RejectOverlap <: AbstractCombinationAlgebra end

"""
    AdditiveAlgebra()

Combines overlapping `Add` effects by addition.
"""
struct AdditiveAlgebra <: AbstractCombinationAlgebra end

"""
    MultiplicativeAlgebra()

Combines overlapping `Scale` effects by multiplication.
"""
struct MultiplicativeAlgebra <: AbstractCombinationAlgebra end

"""
    LatestWins()

Combines overlapping effects by taking the later/program-right effect.
"""
struct LatestWins <: AbstractCombinationAlgebra end

combine_effect(::AbstractCombinationAlgebra, ::AbstractEffect, ::AbstractEffect) = nothing
combine_effect(::AdditiveAlgebra, a::Add, b::Add) = Add(a.delta + b.delta)
combine_effect(::MultiplicativeAlgebra, a::Scale, b::Scale) = Scale(a.factor * b.factor)
combine_effect(::LatestWins, ::AbstractEffect, b::AbstractEffect) = b

"""
    Target(name; kind=Parameter, value_type=Any, algebra=RejectOverlap())

A typed intervention target. Overlapping interventions on the same target are
rejected unless `algebra` supplies a combination rule. `value_type` is enforced
when constructing absolute effects and when applying effects.
"""
struct Target
    name::Symbol
    kind::TargetKind
    value_type::Type
    algebra::AbstractCombinationAlgebra
end

Target(name::Symbol; kind::TargetKind=Parameter, value_type::Type=Any,
       algebra::AbstractCombinationAlgebra=RejectOverlap()) =
    Target(name, kind, value_type, algebra)

Base.:(==)(a::Target, b::Target) = a.name == b.name && a.kind == b.kind
Base.isequal(a::Target, b::Target) = a == b
Base.hash(t::Target, h::UInt) = hash((t.name, t.kind), h)
Base.show(io::IO, t::Target) = print(io, "$(t.kind):$(t.name)")

function _check_value_type(target::Target, value, context::AbstractString)
    target.value_type === Any && return value
    value isa target.value_type && return value
    throw(ArgumentError("$context for target $(target) must be of type $(target.value_type); got $(typeof(value))"))
end

_validate_effect_type(::Target, ::AbstractEffect) = nothing
function _validate_effect_type(target::Target, effect::SetValue)
    _check_value_type(target, effect.value, "SetValue")
    return nothing
end

function _checked_apply_effect(target::Target, effect::AbstractEffect, value)
    _check_value_type(target, value, "Baseline value")
    result = apply_effect(effect, value)
    _check_value_type(target, result, "Intervention result")
    return result
end

"""
    InterventionAtom(id, target, support, effect; metadata=Dict())

A local, typed, temporal edit to a model narrative.
"""
struct InterventionAtom
    id::Symbol
    target::Target
    support::Interval
    effect::AbstractEffect
    metadata::Dict{Symbol,Any}
end

InterventionAtom(id::Symbol, target::Target, support::Interval, effect::AbstractEffect;
                 metadata::Dict{Symbol,Any}=Dict{Symbol,Any}()) = begin
    _validate_effect_type(target, effect)
    InterventionAtom(id, target, support, effect, metadata)
end

Base.show(io::IO, a::InterventionAtom) =
    print(io, "$(a.id): $(a.target) $(a.effect) on $(a.support)")

"""
    InterventionProgram(atoms...)

A finite set/list of intervention atoms. Program order is used only by
non-commutative algebras such as `LatestWins`.
"""
struct InterventionProgram
    atoms::Vector{InterventionAtom}
end

InterventionProgram() = InterventionProgram(InterventionAtom[])
InterventionProgram(atoms::InterventionAtom...) = InterventionProgram(collect(atoms))
InterventionProgram(atoms::AbstractVector{<:InterventionAtom}) = InterventionProgram(collect(atoms))

Base.length(p::InterventionProgram) = length(p.atoms)
Base.iterate(p::InterventionProgram, args...) = iterate(p.atoms, args...)
Base.show(io::IO, p::InterventionProgram) = print(io, "InterventionProgram($(length(p)) atoms)")

"""
    Conflict

Structured report for a same-target overlapping intervention conflict.
"""
struct Conflict
    target::Target
    overlap::Interval
    left::InterventionAtom
    right::InterventionAtom
    reason::String
end

Base.show(io::IO, c::Conflict) =
    print(io, "Conflict(target=$(c.target), overlap=$(c.overlap), reason=$(c.reason))")

struct InterventionConflictError <: Exception
    conflicts::Vector{Conflict}
end

@doc """
    InterventionConflictError(conflicts)

Exception thrown when an intervention program contains unresolved conflicts.
The `conflicts` field stores the vector of [`Conflict`](@ref) reports.
""" InterventionConflictError

function Base.showerror(io::IO, err::InterventionConflictError)
    println(io, "Intervention program has $(length(err.conflicts)) conflict(s):")
    for c in err.conflicts
        println(io, "  - ", c)
    end
end

function _combined_effect(algebra::AbstractCombinationAlgebra, a::AbstractEffect, b::AbstractEffect)
    combined = combine_effect(algebra, a, b)
    return combined
end

function _conflict_for_pair(a::InterventionAtom, b::InterventionAtom)
    a.target == b.target || return nothing
    ov = intersection(a.support, b.support)
    isnothing(ov) && return nothing

    typeof(a.target.algebra) == typeof(b.target.algebra) ||
        return Conflict(a.target, ov, a, b, "target has incompatible combination algebras")

    combined = _combined_effect(a.target.algebra, a.effect, b.effect)
    isnothing(combined) || return nothing
    return Conflict(a.target, ov, a, b, "no combination algebra for overlapping effects")
end

"""
    conflicts(program) -> Vector{Conflict}

Return all same-target overlapping conflicts. Different targets always compose;
same-target disjoint intervals glue; same-target overlaps require an algebra.
"""
function conflicts(program::InterventionProgram)
    result = Conflict[]
    for i in eachindex(program.atoms), j in (i + 1):length(program.atoms)
        c = _conflict_for_pair(program.atoms[i], program.atoms[j])
        isnothing(c) || push!(result, c)
    end
    return result
end

"""
    validate(program) -> Bool

Return `true` when an intervention program has no unresolved same-target
overlap conflicts.
"""
validate(program::InterventionProgram) = isempty(conflicts(program))

"""
    compose_interventions(programs...; check=true) -> InterventionProgram

Compose intervention programs by concatenating atoms, optionally rejecting
same-target overlaps that cannot be glued.
"""
function compose_interventions(programs::InterventionProgram...; check::Bool=true)
    program = InterventionProgram(reduce(vcat, (p.atoms for p in programs); init=InterventionAtom[]))
    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end
    return program
end

"""
    Epoch

An interval in the common refinement of all intervention supports, together
with active atoms and their combined effects by target.
"""
struct Epoch
    support::Interval
    atoms::Vector{InterventionAtom}
    effects::Dict{Target,AbstractEffect}
end

Base.show(io::IO, e::Epoch) =
    print(io, "Epoch($(e.support), targets=$(collect(keys(e.effects))))")

function _combine_active(active::Vector{InterventionAtom})
    effects = Dict{Target,AbstractEffect}()
    for atom in active
        key = atom.target
        if haskey(effects, key)
            existing = getkey(effects, key, key)
            typeof(existing.algebra) == typeof(atom.target.algebra) ||
                throw(InterventionConflictError([Conflict(existing, atom.support, atom, atom,
                    "target has incompatible combination algebras")]))
            combined = _combined_effect(existing.algebra, effects[existing], atom.effect)
            if isnothing(combined)
                ov = atom.support
                throw(InterventionConflictError([Conflict(existing, ov, atom, atom,
                    "no combination algebra for overlapping effects")]))
            end
            effects[existing] = combined
        else
            effects[key] = atom.effect
        end
    end
    return effects
end

"""
    epochize(program; check=true) -> Vector{Epoch}

Compute the common interval refinement induced by all intervention endpoints.
Each returned epoch is labeled by the interventions active on that epoch.
"""
function epochize(program::InterventionProgram; check::Bool=true)
    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end
    isempty(program.atoms) && return Epoch[]

    boundaries = sort(unique(vcat([a.support.start for a in program.atoms],
                                  [a.support.stop for a in program.atoms])))
    epochs = Epoch[]
    for i in 1:(length(boundaries) - 1)
        support = Interval(boundaries[i], boundaries[i + 1])
        active = [atom for atom in program.atoms if overlaps(atom.support, support)]
        isempty(active) && continue
        push!(epochs, Epoch(support, active, _combine_active(active)))
    end
    return epochs
end

"""
    EpochValues

Values induced by applying an intervention program to a baseline on an epoch.
"""
struct EpochValues
    support::Interval
    values::Dict{Symbol,Any}
    atoms::Vector{InterventionAtom}
end

"""
    apply_interventions(program, baseline) -> Vector{EpochValues}

Apply a program to a baseline dictionary on each active epoch.
"""
function apply_interventions(program::InterventionProgram, baseline::Dict{Symbol,<:Any}; check::Bool=true)
    _check_symbol_keyed_targets(program)
    result = EpochValues[]
    for epoch in epochize(program; check)
        values = Dict{Symbol,Any}(k => v for (k, v) in baseline)
        for (target, effect) in epoch.effects
            name = target.name
            haskey(values, name) || error("Baseline value missing for target :$name")
            values[name] = _checked_apply_effect(target, effect, values[name])
        end
        push!(result, EpochValues(epoch.support, values, epoch.atoms))
    end
    return result
end

function _check_symbol_keyed_targets(program::InterventionProgram)
    seen = Dict{Symbol,TargetKind}()
    for atom in program.atoms
        name = atom.target.name
        if haskey(seen, name) && seen[name] != atom.target.kind
            error("Symbol-keyed application cannot disambiguate target :$name used as both $(seen[name]) and $(atom.target.kind)")
        end
        seen[name] = atom.target.kind
    end
    return nothing
end

"""
    apply_discrete(program, baseline, times) -> Dict

Apply interventions componentwise to vector-valued discrete-time schedules.
Immutable baseline schedules are materialized into mutable output vectors.
"""
function apply_discrete(program::InterventionProgram, baseline::Dict{Symbol,<:AbstractVector},
                        times::AbstractVector; check::Bool=true)
    _check_symbol_keyed_targets(program)
    length_values = unique(length(v) for v in values(baseline))
    length(length_values) == 1 || error("All baseline schedules must have the same length")
    only(length_values) == length(times) || error("Baseline schedule length must match times")

    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end

    output = Dict{Symbol,Any}(k => collect(v) for (k, v) in baseline)
    for (idx, t) in enumerate(times)
        active = [atom for atom in program.atoms if contains_time(atom.support, t)]
        effects = _combine_active(active)
        for (target, effect) in effects
            name = target.name
            haskey(output, name) || error("Baseline schedule missing for target :$name")
            output[name][idx] = _checked_apply_effect(target, effect, baseline[name][idx])
        end
    end
    return output
end

"""
    PetriIndexing(; parameters, states=Symbol[])
    PetriIndexing(parameters, states=Symbol[])

Map named intervention targets to selectors for SciML state (`integrator.u`) and
parameter/rate (`integrator.p`) vectors. A vector of names maps each target to its
own label, which is the preferred AlgebraicPetri/LabelledArrays representation.
Use dictionaries such as `Dict(:beta => 1)` only for unlabeled vectors.
"""
struct PetriIndexing
    parameters::Dict{Symbol,Any}
    states::Dict{Symbol,Any}
end

_selector(name::Symbol) = name
_selector(name::AbstractString) = Symbol(name)
_selector(index::Integer) = Int(index)
_selector(selector) = selector

function _selector_dict(names::AbstractVector)
    return Dict{Symbol,Any}(Symbol(name) => _selector(name) for name in names)
end

_selector_dict(names::AbstractDict) =
    Dict{Symbol,Any}(Symbol(name) => _selector(selector) for (name, selector) in pairs(names))

PetriIndexing(parameters::Union{AbstractVector,AbstractDict},
              states::Union{AbstractVector,AbstractDict}=Symbol[]) =
    PetriIndexing(_selector_dict(parameters), _selector_dict(states))

PetriIndexing(; parameters, states=Symbol[]) = PetriIndexing(parameters, states)

_is_parameter_like(target::Target) =
    target.kind == Parameter || target.kind == Process || target.kind == Observation

function _parameter_selector(indexing::PetriIndexing, target::Target)
    _is_parameter_like(target) || error("Target $(target.name) is not parameter-like")
    haskey(indexing.parameters, target.name) || error("No parameter selector for target :$(target.name)")
    return indexing.parameters[target.name]
end

function _state_selector(indexing::PetriIndexing, target::Target)
    target.kind == State || error("Target $(target.name) is not a state target")
    haskey(indexing.states, target.name) || error("No state selector for target :$(target.name)")
    return indexing.states[target.name]
end

"""
    callback_times(program)

Return all event times needed to lower an intervention program to callbacks.
Parameter-like targets contribute start and stop times; state targets contribute
their start times and are treated as pulses by default.
"""
function callback_times(program::InterventionProgram)
    times = Any[]
    for atom in program.atoms
        if atom.target.kind == State
            push!(times, atom.support.start)
        else
            push!(times, atom.support.start)
            push!(times, atom.support.stop)
        end
    end
    return sort(unique(times))
end

"""
    active_parameter_effects(program, t)

Combined parameter/process/observation effects active at time `t`.
"""
function active_parameter_effects(program::InterventionProgram, t; check::Bool=true)
    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end
    active = [atom for atom in program.atoms
              if _is_parameter_like(atom.target) && contains_time(atom.support, t)]
    return _combine_active(active)
end

"""
    state_pulses_at(program, t)

Combined state effects whose support starts at time `t`.
State interventions lower to instantaneous callback pulses.
"""
function state_pulses_at(program::InterventionProgram, t; check::Bool=true)
    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end
    active = [atom for atom in program.atoms
              if atom.target.kind == State && atom.support.start == t]
    return _combine_active(active)
end

_mutable_vector!(x, name) =
    x isa AbstractVector || error("$name must be a mutable vector; got $(typeof(x))")

function _parameter_targets(program::InterventionProgram)
    targets = Target[]
    for atom in program.atoms
        if _is_parameter_like(atom.target) && !(atom.target in targets)
            push!(targets, atom.target)
        end
    end
    return targets
end

"""
    apply_parameter_effects!(p, program, indexing, baseline_p, t)

Reset only the program-targeted parameter selectors to `baseline_p`, then apply
all parameter-like effects active at `t`. Untargeted parameters are left
unchanged so independent callbacks can compose safely.
"""
function apply_parameter_effects!(p::AbstractVector, program::InterventionProgram,
                                  indexing::PetriIndexing, baseline_p::AbstractVector, t;
                                  check::Bool=true)
    length(p) == length(baseline_p) || error("Parameter vector and baseline_p lengths differ")
    for target in _parameter_targets(program)
        selector = _parameter_selector(indexing, target)
        _check_value_type(target, baseline_p[selector], "Baseline value")
        p[selector] = baseline_p[selector]
    end
    effects = active_parameter_effects(program, t; check)
    for (target, effect) in effects
        selector = _parameter_selector(indexing, target)
        p[selector] = _checked_apply_effect(target, effect, baseline_p[selector])
    end
    return p
end

"""
    apply_state_pulses!(u, program, indexing, t)

Apply state pulses scheduled at `t` to the current state vector `u`.
Unlike parameters, states are not reset to a baseline.
"""
function apply_state_pulses!(u::AbstractVector, program::InterventionProgram,
                             indexing::PetriIndexing, t; check::Bool=true)
    effects = state_pulses_at(program, t; check)
    for (target, effect) in effects
        selector = _state_selector(indexing, target)
        u[selector] = _checked_apply_effect(target, effect, u[selector])
    end
    return u
end

"""
    apply_to_integrator!(integrator, program, indexing, t; baseline_p)

Mutate a SciML-style integrator in place. This function assumes AlgebraicPetri-style
ODE problems where rates/parameters live in `integrator.p` and states live in
`integrator.u`.
"""
function apply_to_integrator!(integrator, program::InterventionProgram,
                              indexing::PetriIndexing, t;
                              baseline_p=nothing, check::Bool=true)
    if baseline_p !== nothing
        _mutable_vector!(integrator.p, "integrator.p")
        apply_parameter_effects!(integrator.p, program, indexing, baseline_p, t; check)
    end
    _mutable_vector!(integrator.u, "integrator.u")
    apply_state_pulses!(integrator.u, program, indexing, t; check)
    return integrator
end

"""
    to_callback(program, indexing; kwargs...)

Lower an intervention program to a DiffEqCallbacks.jl callback. Load
`DiffEqCallbacks` to activate this method.
"""
function to_callback end

include("operators.jl")

"""
    epoch_finfunction(times, epochs) -> FinFunction

Use Catlab to represent the map from sampled time points to intervention epochs.
"""
function epoch_finfunction(times::AbstractVector, epochs::AbstractVector{<:Union{Epoch,Interval}})
    intervals = [e isa Epoch ? e.support : e for e in epochs]
    assignments = Int[]
    for t in times
        idx = findfirst(I -> contains_time(I, t), intervals)
        isnothing(idx) && error("Time $t does not lie in any epoch")
        push!(assignments, idx)
    end
    return FinFunction(assignments, FinSet(length(times)), FinSet(length(intervals)))
end

@present SchInterventionProgram(FreeSchema) begin
    (Atom, TargetObj)::Ob
    target::Hom(Atom, TargetObj)
    (IdT, NameT, KindT, TimeT, ModeT, ValueT)::AttrType
    atom_id::Attr(Atom, IdT)
    target_name::Attr(TargetObj, NameT)
    target_kind::Attr(TargetObj, KindT)
    start::Attr(Atom, TimeT)
    stop::Attr(Atom, TimeT)
    mode::Attr(Atom, ModeT)
    value::Attr(Atom, ValueT)
end

@acset_type InterventionProgramData(SchInterventionProgram, index=[:target])

@doc """
    InterventionProgramData

Catlab ACSet type used by `as_acset` to encode intervention atoms, targets,
supports, and effect labels as categorical data.
""" InterventionProgramData

"""
    as_acset(program) -> InterventionProgramData

Encode an intervention program as a Catlab ACSet. Attributes are stringified so
programs with heterogeneous time and value types can still be inspected uniformly.
"""
function as_acset(program::InterventionProgram)
    unique_targets = Target[]
    for atom in program.atoms
        atom.target in unique_targets || push!(unique_targets, atom.target)
    end
    target_index = Dict(t => i for (i, t) in enumerate(unique_targets))

    acset = InterventionProgramData{String,String,String,String,String,String}()
    add_parts!(acset, :TargetObj, length(unique_targets))
    set_subpart!(acset, :target_name, string.(getfield.(unique_targets, :name)))
    set_subpart!(acset, :target_kind, string.(getfield.(unique_targets, :kind)))

    add_parts!(acset, :Atom, length(program.atoms))
    set_subpart!(acset, :target, [target_index[atom.target] for atom in program.atoms])
    set_subpart!(acset, :atom_id, string.(getfield.(program.atoms, :id)))
    set_subpart!(acset, :start, [string(atom.support.start) for atom in program.atoms])
    set_subpart!(acset, :stop, [string(atom.support.stop) for atom in program.atoms])
    set_subpart!(acset, :mode, [string(effect_mode(atom.effect)) for atom in program.atoms])
    set_subpart!(acset, :value, [string(atom.effect) for atom in program.atoms])
    return acset
end

end # module
