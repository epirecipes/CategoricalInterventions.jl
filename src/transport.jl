"""
Transport of programs along maps of targets.

A model morphism induces a map of targets. `pushforward` renames atoms along it;
`lift` pulls a program back along a projection from a stratified model to its
base, placing a copy of each atom on every stratum. Both are functorial, and
both preserve conflict-freeness under the stated conditions (Lean:
`pushforward_comp`, `lift_comp`, `conflictFree_pushforward_of_injOn`,
`conflictFree_lift_iff`).
"""

_target_map(f::Dict{Target,Target}) = t -> get(f, t, t)
_target_map(f::Dict{Symbol,Symbol}) = t -> Target(get(f, t.name, t.name), t.kind)
_target_map(f::Function) = f

function _rename_effect(e::Transfer, f)
    Transfer(f(Target(e.to, State)).name, e.amount)
end
function _rename_effect(e::Flow, f)
    Flow(f(Target(e.to, State)).name, e.rate)
end
_rename_effect(e::AbstractEffect, f) = e

"""
    pushforward(program, f; space=nothing) -> Program

Rename every atom's target along `f`, a `Dict{Target,Target}`,
`Dict{Symbol,Symbol}`, or function on targets. Targets not in the map are kept.
If `f` merges targets, new conflicts may appear and are reported. The new
declaration table is `space` if given, else the old table transported along
`f`.
"""
function pushforward(p::Program, f; space::Union{Nothing,TargetSpace}=nothing, check::Bool=true)
    g = _target_map(f)
    atoms = Atom[Atom(a.id, g(a.target), a.support, _rename_effect(a.effect, g), a.metadata) for a in p.atoms]
    sp = space === nothing ? _transport_space(p.space, g) : space
    out = Program(atoms, sp)
    check && check_conflicts(out)
    return out
end

function _transport_space(space::TargetSpace, g)
    out = TargetSpace(; default=space.default)
    for (t, s) in space.specs
        out.specs[g(t)] = s
    end
    return out
end

"""
    fibres(π) -> Dict{Target, Vector{Target}}

Group the domain of a projection `π::Dict{Target,Target}` by image.
"""
function fibres(π::Dict{Target,Target})
    out = Dict{Target,Vector{Target}}()
    for (t′, t) in π
        push!(get!(out, t, Target[]), t′)
    end
    for v in values(out)
        sort!(v; by=t -> string(t.name))
    end
    return out
end

"""
    lift(program, π; strata=Dict(), space=nothing) -> Program

Pull a program back along a projection `π::Dict{Target,Target}` from the
targets of a stratified model to the targets of its base. Each atom on base
target `j` becomes one atom on each `j′` with `π[j′] == j`, with id suffixed by
the new target name. A `Transfer` needs `strata`, a `Dict{Target,Any}` naming
the stratum of each stratified target, so the destination is matched within
the same stratum. Undeclared new targets inherit their base target's
declaration.
"""
function lift(p::Program, π::Dict{Target,Target}; strata::Dict{Target,<:Any}=Dict{Target,Any}(),
              space::Union{Nothing,TargetSpace}=nothing, check::Bool=true)
    fib = fibres(π)
    atoms = Atom[]
    for a in p.atoms
        haskey(fib, a.target) || error("Target $(a.target) has no preimage under the projection")
        for t′ in fib[a.target]
            eff = a.effect
            if eff isa Transfer || eff isa Flow
                dest = Target(eff.to, State)
                haskey(fib, dest) || error("Destination $(dest) has no preimage under the projection")
                cands = fib[dest]
                if length(cands) == 1
                    dest′ = only(cands)
                else
                    haskey(strata, t′) || error("lift needs `strata` to match the destination of $(a.id) within a stratum")
                    matches = [d for d in cands if get(strata, d, nothing) == strata[t′]]
                    length(matches) == 1 || error("No unique destination for $(a.id) in stratum $(strata[t′])")
                    dest′ = only(matches)
                end
                eff = eff isa Transfer ? Transfer(dest′.name, eff.amount) : Flow(dest′.name, eff.rate)
            end
            push!(atoms, Atom(Symbol(a.id, "_", t′.name), t′, a.support, eff, a.metadata))
        end
    end
    sp = space
    if sp === nothing
        sp = TargetSpace(; default=p.space.default)
        for (t′, t) in π
            sp.specs[t′] = spec(p.space, t)
        end
    end
    out = Program(atoms, sp)
    check && check_conflicts(out)
    return out
end

"""
    lift_along(program, π; kwargs...)

The same as [`lift`](@ref). Use it when `Catlab` is also loaded, since Catlab
exports a different `lift`.
"""
lift_along(p::Program, π; kw...) = lift(p, π; kw...)

"""
    lift(program, π::Dict{Symbol,Symbol}; kinds...)

Convenience: a projection given on names; kinds are taken from the program's
atoms.
"""
function lift(p::Program, π::Dict{Symbol,Symbol}; kw...)
    kinds = Dict{Symbol,TargetKind}()
    for a in p.atoms, t in atom_targets(a)
        kinds[t.name] = t.kind
    end
    for a in p.atoms
        (a.effect isa Transfer || a.effect isa Flow) && (kinds[a.effect.to] = State)
    end
    πt = Dict{Target,Target}()
    for (n′, n) in π
        haskey(kinds, n) || continue
        πt[Target(n′, kinds[n])] = Target(n, kinds[n])
    end
    return lift(p, πt; kw...)
end
