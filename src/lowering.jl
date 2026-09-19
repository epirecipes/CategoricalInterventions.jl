"""
Lowering: from a program to discrete events on an integrator.

Events are the endpoints of spans and the times of instants. At each event the
targeted parameters are reset to baseline and the active effects applied; pulses
whose instant equals the event time mutate the state. Holding each value until
the next event reproduces the program's schedule exactly (Lean:
`lower_eq_apply`). Nothing here depends on DifferentialEquations; the
DiffEqCallbacks extension wraps these functions in a `PresetTimeCallback`.
"""

_indexing(m::Model) = m.indexing
_indexing(i::Indexing) = i
_invariants(m::Model) = m.invariants
_invariants(::Indexing) = AbstractInvariant[]
_space(m::Model) = m.space
_space(::Indexing) = nothing

"""
    event_times(program) -> Vector

All times at which the callback must fire: span endpoints and instants.
"""
function event_times(p::Program)
    ts = [t for a in p.atoms for t in endpoints(a.support)]
    isempty(ts) && return Float64[]
    T = promote_type(typeof.(ts)...)
    return sort!(unique!(T[t for t in ts]))
end
const callback_times = event_times

function _check_container(x, sel, what)
    sel isa Symbol && x isa Vector &&
        error("$what is a plain Vector but the model locates :$sel by label; pass a labelled container " *
              "(LVector or ComponentArray) or build the model with positional selectors such as Dict(:$sel => 1)")
    return nothing
end

function _parameter_selector(ix::Indexing, t::Target)
    is_parameter_like(t) || error("Target $t is not parameter-like")
    haskey(ix.parameters, t.name) || error("No parameter selector for target :$(t.name)")
    return ix.parameters[t.name]
end
function _state_selector(ix::Indexing, t::Target)
    is_state(t) || error("Target $t is not a state target")
    haskey(ix.states, t.name) || error("No state selector for target :$(t.name)")
    return ix.states[t.name]
end

"""
    active_parameter_effects(program, t) -> Dict{Target, effect}

Combined parameter-like effects active at `t`.
"""
function active_parameter_effects(p::Program, t; check::Bool=true)
    eff = active_effects(p, t; check)
    return Dict{Target,AbstractEffect}(k => v for (k, v) in eff if is_parameter_like(k) && v !== nothing)
end

"""
    state_pulses_at(program, t) -> Dict{Target, effect}

Combined pulse effects whose instant is exactly `t`, per state target.
"""
function state_pulses_at(p::Program, t; check::Bool=true)
    check && check_conflicts(p)
    pulses = Atom[a for a in p.atoms if a.support isa Instant && a.support.t == t]
    eff = _fold_all(p, pulses)
    return Dict{Target,AbstractEffect}(k => v for (k, v) in eff if is_state(k) && v !== nothing)
end

parameter_targets(p::Program) = unique(Target[t for a in p.atoms for t in atom_targets(a) if is_parameter_like(t)])

"""
    apply_parameter_effects!(p, program, model, baseline_p, t)

Reset the program's parameter targets to `baseline_p`, then apply the effects
active at `t`. Untargeted entries are untouched so independent callbacks
compose.
"""
function apply_parameter_effects!(pvec, prog::Program, m, baseline_p, t; check::Bool=true)
    ix = _indexing(m)
    pvec isa AbstractVector && baseline_p isa AbstractVector && length(pvec) != length(baseline_p) &&
        error("Parameter vector and baseline_p lengths differ")
    for target in parameter_targets(prog)
        sel = _parameter_selector(ix, target)
        _check_container(pvec, sel, "integrator.p")
        _setp!(pvec, sel, _getp(baseline_p, sel))
    end
    for (target, eff) in active_parameter_effects(prog, t; check)
        sel = _parameter_selector(ix, target)
        _setp!(pvec, sel, _apply_checked(prog, target, eff, _getp(baseline_p, sel)))
    end
    return pvec
end

"""
    apply_state_pulses!(u, program, model, t)

Apply the pulses scheduled at `t` to the state vector, then check the model's
invariants.
"""
function apply_state_pulses!(u, prog::Program, m, t; check::Bool=true)
    ix = _indexing(m)
    pulses = state_pulses_at(prog, t; check)
    isempty(pulses) && return u
    before = copy(u)
    for (target, eff) in pulses
        sel = _state_selector(ix, target)
        _check_container(u, sel, "integrator.u")
        _setp!(u, sel, _apply_checked(prog, target, eff, _getp(u, sel)))
    end
    m isa Model && check_invariants(m, before, u)
    return u
end

"""
    apply_to_integrator!(integrator, program, model, t; baseline_p=nothing)

Mutate a SciML-style integrator in place at event time `t`.
"""
function apply_to_integrator!(integrator, prog::Program, m, t; baseline_p=nothing, check::Bool=true)
    if baseline_p !== nothing
        apply_parameter_effects!(integrator.p, prog, m, baseline_p, t; check)
    end
    apply_state_pulses!(integrator.u, prog, m, t; check)
    return integrator
end

"""
    lower(program, baseline::Dict{Symbol}) -> Vector{Pair{time, Dict{Symbol,Any}}}

The pure event table: at each event time, the parameter values that the
callback will set. `hold_last(table, t)` reads it back.
"""
function lower(p::Program, baseline::Dict{Symbol,<:Any}; check::Bool=true)
    check && check_conflicts(p)
    table = Pair{Any,Dict{Symbol,Any}}[]
    for t in event_times(p)
        vals = Dict{Symbol,Any}(k => v for (k, v) in baseline)
        for (target, eff) in active_parameter_effects(p, t; check=false)
            vals[target.name] = _apply_checked(p, target, eff, baseline[target.name])
        end
        push!(table, t => vals)
    end
    return table
end

"""
    hold_last(table, baseline, t)

Value from the last event at or before `t`, or the baseline before any event.
"""
function hold_last(table, baseline::Dict{Symbol,<:Any}, t)
    vals = Dict{Symbol,Any}(k => v for (k, v) in baseline)
    for (te, v) in table
        te <= t || break
        vals = v
    end
    return vals
end

"""
    to_callback(program, model; baseline_p=nothing, save_positions=(true, true))

Lower a program to a `DiffEqCallbacks.PresetTimeCallback`. Load
`DiffEqCallbacks` to activate this method.
"""
function to_callback end

"""
    simulate(model, program; u0, p0, tspan, saveat, alg, kwargs...)

Build the problem for `model`, attach the program's callback, and solve. Load
`DiffEqCallbacks` and an integrator package to activate this method.
"""
function simulate end
