"""
Semantics: what a program does to a schedule.

A schedule assigns a value to each target at each time. A conflict-free program
acts pointwise: at time `t`, the combined effect of the active atoms is applied
to the baseline value. Application is local, a homomorphism in the program, and
commutes with restriction and resampling of the schedule (Lean: `apply_local`,
`apply_append`, `apply_pullback`).
"""

function _check_symbol_keyed_targets(p::Program)
    seen = Dict{Symbol,TargetKind}()
    for a in p.atoms, t in atom_targets(a)
        if haskey(seen, t.name) && seen[t.name] != t.kind
            error("Symbol-keyed application cannot disambiguate target :$(t.name) used as both " *
                  "$(seen[t.name]) and $(t.kind)")
        end
        seen[t.name] = t.kind
    end
    return nothing
end

function _apply_checked(p::Program, target::Target, effect::AbstractEffect, value)
    vt = value_type(p.space, target)
    _check_value_type(vt, value, "Baseline value", target)
    out = apply_effect(effect, value)
    _check_value_type(vt, out, "Intervention result", target)
    return out
end

"""
    EpochValues

Values induced on one epoch by applying a program to a scalar baseline.
"""
struct EpochValues
    support::Span
    values::Dict{Symbol,Any}
    atoms::Vector{Atom}
end

"""
    apply(program, baseline::Dict{Symbol}) -> Vector{EpochValues}

Apply a program to scalar baseline values, one result per epoch. Span atoms
only; pulses are events, not schedule edits.
"""
function apply(p::Program, baseline::Dict{Symbol,<:Any}; check::Bool=true)
    _check_symbol_keyed_targets(p)
    out = EpochValues[]
    for e in epochs(p; check)
        values = Dict{Symbol,Any}(k => v for (k, v) in baseline)
        for (t, eff) in e.effects
            eff === nothing && continue
            haskey(values, t.name) || error("Baseline value missing for target :$(t.name)")
            values[t.name] = _apply_checked(p, t, eff, values[t.name])
        end
        push!(out, EpochValues(e.support, values, e.atoms))
    end
    return out
end
const apply_interventions = apply

"""
    apply(program, baseline::Dict{Symbol,<:AbstractVector}, times) -> Dict

Apply a program pointwise to time-indexed schedules. State pulses at a grid
time are applied to that grid point's value (the pre-update convention) when
the state's schedule is supplied, and ignored otherwise.
"""
function apply(p::Program, baseline::Dict{Symbol,<:AbstractVector}, times::AbstractVector; check::Bool=true)
    _check_symbol_keyed_targets(p)
    lengths = unique(length(v) for v in values(baseline))
    length(lengths) == 1 || error("All baseline schedules must have the same length")
    only(lengths) == length(times) || error("Baseline schedule length must match times")
    check && check_conflicts(p)
    out = Dict{Symbol,Any}(k => collect(v) for (k, v) in baseline)
    for (i, t) in enumerate(times)
        for (target, eff) in active_effects(p, t; check=false)
            eff === nothing && continue
            if !haskey(out, target.name)
                is_state(target) && continue   # pulses touch only the state schedules supplied
                error("Baseline schedule missing for target :$(target.name)")
            end
            out[target.name][i] = _apply_checked(p, target, eff, baseline[target.name][i])
        end
    end
    return out
end
apply_discrete(p::Program, baseline, times; kw...) = apply(p, baseline, times; kw...)

"""
    sample(program, grid::AbstractRange) -> Program

Pull a program back along the grid map `k ↦ grid[k]`: each span `[a, b)`
becomes the span of grid indices `k` with `a ≤ grid[k] < b`, and each instant
becomes the index of the matching grid point (an instant off the grid is
dropped with a warning). Applying the sampled program at indices agrees with
applying the original at grid values (Lean: `apply_pullback`,
`grid_preimage_span`).
"""
function sample(p::Program, grid::AbstractRange)
    t0, Δ = first(grid), step(grid)
    n = length(grid)
    atoms = Atom[]
    for a in p.atoms
        if a.support isa Span
            lo = ceil(Int, (a.support.lo - t0) / Δ) + 1
            hi = ceil(Int, (a.support.hi - t0) / Δ) + 1
            lo = max(lo, 1); hi = min(hi, n + 1)
            lo < hi || continue
            push!(atoms, Atom(a.id, a.target, Span(lo, hi), a.effect, a.metadata))
        else
            k = round((a.support.t - t0) / Δ)
            if abs(k * Δ + t0 - a.support.t) > sqrt(eps(float(Δ))) * max(1, abs(Δ))
                @warn "Instant $(a.support.t) of atom $(a.id) is not on the grid; dropped"
                continue
            end
            idx = Int(k) + 1
            1 <= idx <= n || continue
            push!(atoms, Atom(a.id, a.target, Instant(idx), a.effect, a.metadata))
        end
    end
    return Program(atoms, p.space)
end
