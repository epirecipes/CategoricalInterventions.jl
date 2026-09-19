"""
Targets, atoms, programs, conflicts, composition, and epochs.
"""

# ---------------------------------------------------------------- targets ---

@enum TargetKind Parameter State Process Observation

@doc "Target kind for model parameters or rates." Parameter
@doc "Target kind for state variables. State interventions are pulses or flows." State
@doc "Target kind for process-level quantities; treated like parameters." Process
@doc "Target kind for observation-level quantities; treated like parameters." Observation

"""
    Target(name; kind=Parameter)

What an intervention changes: a named parameter, state, process, or
observation. Identity is `(name, kind)`; the value type and combination
algebra live on the [`TargetSpace`](@ref) of a model, not on the target.
"""
struct Target
    name::Symbol
    kind::TargetKind
end
Target(name::Symbol; kind::TargetKind=Parameter) = Target(name, kind)
Target(name::AbstractString; kind::TargetKind=Parameter) = Target(Symbol(name), kind)

Base.show(io::IO, t::Target) = print(io, t.kind, ":", t.name)

is_parameter_like(t::Target) = t.kind != State
is_state(t::Target) = t.kind == State

"""
    TargetSpec(; value_type=Any, algebra=Reject())

Per-target declaration: the value type enforced on absolute effects and results,
and the algebra used to combine overlapping effects.
"""
struct TargetSpec
    value_type::Type
    algebra::AbstractAlgebra
end
TargetSpec(; value_type::Type=Any, algebra::AbstractAlgebra=Reject()) =
    TargetSpec(value_type, algebra)

"""
    TargetSpace(; default=Reject())

The table of declared targets of a model. Undeclared targets fall back to the
`default` algebra and value type `Any`.
"""
struct TargetSpace
    specs::Dict{Target,TargetSpec}
    default::AbstractAlgebra
end
TargetSpace(; default::AbstractAlgebra=Reject()) = TargetSpace(Dict{Target,TargetSpec}(), default)

"""
    declare!(space, target, algebra; value_type=Any)

Declare (or redeclare) the algebra and value type of a target.
"""
function declare!(space::TargetSpace, target::Target, algebra::AbstractAlgebra;
                  value_type::Type=Any)
    space.specs[target] = TargetSpec(value_type, algebra)
    return space
end
declare!(space::TargetSpace, name::Symbol, algebra::AbstractAlgebra; kind::TargetKind=Parameter, kw...) =
    declare!(space, Target(name, kind), algebra; kw...)

spec(space::TargetSpace, t::Target) = get(space.specs, t, TargetSpec(Any, space.default))
algebra(space::TargetSpace, t::Target) = spec(space, t).algebra
value_type(space::TargetSpace, t::Target) = spec(space, t).value_type
targets(space::TargetSpace) = collect(keys(space.specs))

"""
    merge(a::TargetSpace, b::TargetSpace)

Union of two declaration tables. Targets declared in both must agree.
"""
function Base.merge(a::TargetSpace, b::TargetSpace)
    specs = copy(a.specs)
    for (t, s) in b.specs
        if haskey(specs, t) && (specs[t].algebra != s.algebra || specs[t].value_type != s.value_type)
            error("Target $t is declared differently in the two programs being composed: " *
                  "$(specs[t].algebra) vs $(s.algebra)")
        end
        specs[t] = s
    end
    default = a.default == b.default ? a.default : (isempty(a.specs) ? b.default : a.default)
    return TargetSpace(specs, default)
end

function _check_value_type(vt::Type, value, context::AbstractString, target::Target)
    vt === Any && return value
    value isa vt && return value
    throw(ArgumentError("$context for target $target must be of type $vt; got $(typeof(value))"))
end

# ------------------------------------------------------------------ atoms ---

"""
    Atom(id, target, support, effect; metadata=Dict())

A local, typed, temporal edit: change `target` by `effect` on `support`.

Well-formedness: parameter-like targets take spans; state targets take an
`Instant` with a pulse effect (`SetValue`, `Add`, `Transfer`) or a `Span` with a
`Flow`.
"""
struct Atom
    id::Symbol
    target::Target
    support::AbstractSupport
    effect::AbstractEffect
    metadata::Dict{Symbol,Any}
    function Atom(id::Symbol, target::Target, support::AbstractSupport, effect::AbstractEffect,
                  metadata::Dict{Symbol,Any})
        _check_wellformed(target, support, effect)
        new(id, target, support, effect, metadata)
    end
end
Atom(id::Symbol, target::Target, support::AbstractSupport, effect::AbstractEffect; metadata=Dict{Symbol,Any}()) =
    Atom(id, target, support, effect, Dict{Symbol,Any}(metadata))

function _check_wellformed(target::Target, support::AbstractSupport, effect::AbstractEffect)
    if is_state(target)
        if effect isa Flow
            support isa Span || throw(ArgumentError("A Flow on state $(target.name) needs a Span support"))
        else
            support isa Instant ||
                throw(ArgumentError("A pulse on state $(target.name) needs an Instant support; " *
                                    "use Instant(t) or `at=t`. For a continuous effect use a Flow."))
        end
    else
        support isa Span ||
            throw(ArgumentError("An effect on $(target) needs a Span support `[lo, hi)`"))
        (effect isa Transfer || effect isa Flow) &&
            throw(ArgumentError("Transfer and Flow effects apply to State targets only"))
    end
    return nothing
end

Base.show(io::IO, a::Atom) = print(io, a.id, ": ", a.target, " ", a.effect, " on ", a.support)

"""
    InterventionAtom(id, target, support, effect; metadata)

Deprecated v0.1 constructor. A `Span` on a `State` target is converted to an
`Instant` at the span start.
"""
function InterventionAtom(id::Symbol, target::Target, support::AbstractSupport, effect::AbstractEffect;
                          metadata::Dict{Symbol,Any}=Dict{Symbol,Any}())
    if is_state(target) && support isa Span && !(effect isa Flow)
        support = Instant(support.lo)
    end
    return Atom(id, target, support, effect, metadata)
end

"""
    expand(atom) -> Vector{Pair{Target,AbstractEffect}}

The per-target effects an atom contributes. A `Transfer` contributes a removal
on its own target and an addition on the destination; a `Flow` contributes
nothing until the model is augmented.
"""
expand(a::Atom) = expand(a, a.effect)
expand(a::Atom, e::Transfer) = Pair{Target,AbstractEffect}[a.target => e, Target(e.to, State) => Add(e.amount)]
expand(a::Atom, ::Flow) = Pair{Target,AbstractEffect}[]
expand(a::Atom, ::AbstractEffect) = Pair{Target,AbstractEffect}[a.target => a.effect]

atom_targets(a::Atom) = first.(expand(a))

# --------------------------------------------------------------- programs ---

"""
    Program(atoms...; space=TargetSpace())

A finite list of atoms together with the declaration table of their targets.
Order matters only under ordered policies.
"""
struct Program
    atoms::Vector{Atom}
    space::TargetSpace
end
Program(atoms::AbstractVector{<:Atom}; space::TargetSpace=TargetSpace()) = Program(collect(atoms), space)
Program(atoms::Atom...; space::TargetSpace=TargetSpace()) = Program(collect(atoms), space)
Program(; space::TargetSpace=TargetSpace()) = Program(Atom[], space)

const InterventionProgram = Program

Base.length(p::Program) = length(p.atoms)
Base.iterate(p::Program, args...) = iterate(p.atoms, args...)
Base.getindex(p::Program, i) = p.atoms[i]
Base.show(io::IO, p::Program) = print(io, "Program(", length(p), " atom", length(p) == 1 ? "" : "s", ")")
Base.:(==)(p::Program, q::Program) = p.atoms == q.atoms && p.space.specs == q.space.specs
algebra(p::Program, t::Target) = algebra(p.space, t)

function Base.:(==)(a::Atom, b::Atom)
    a.id == b.id && a.target == b.target && a.support == b.support && a.effect == b.effect
end

"""
    active(program, t) -> Vector{Atom}

Atoms whose support contains `t`.
"""
active(p::Program, t) = Atom[a for a in p.atoms if t ∈ a.support]
active_spans(p::Program, t) = Atom[a for a in p.atoms if a.support isa Span && t ∈ a.support]

# --------------------------------------------------------------- folding ---

"""
    fold(algebra, contributions) -> (effect, nothing) or (nothing, (i, j))

Combine the effects contributed to one target. `contributions` is a vector of
`(atom, effect)` pairs in program order. Under a PCM the result is the partial
product; under an ordered policy the chosen atom's effect. On failure the
indices of the first non-combining pair are returned.
"""
function fold(alg::AbstractPCM, contributions::Vector{Tuple{Atom,AbstractEffect}})
    acc::AbstractEffect = Identity()
    acc_index = 0
    for (i, (_, e)) in enumerate(contributions)
        c = combine(alg, acc, e)
        c === nothing && return (nothing, (max(acc_index, 1), i))
        acc = c
        acc_index = i
    end
    return (acc, nothing)
end

function fold(::LatestWins, contributions::Vector{Tuple{Atom,AbstractEffect}})
    isempty(contributions) && return (Identity(), nothing)
    return (last(contributions)[2], nothing)
end

function fold(::HighestPriority, contributions::Vector{Tuple{Atom,AbstractEffect}})
    isempty(contributions) && return (Identity(), nothing)
    best = 1
    for i in 2:length(contributions)
        if get(contributions[i][1].metadata, :priority, 0) >= get(contributions[best][1].metadata, :priority, 0)
            best = i
        end
    end
    return (contributions[best][2], nothing)
end

"""
    contributions(atoms) -> Dict{Target, Vector{(atom, effect)}}

Group expanded effects by target, preserving program order.
"""
function contributions(atoms::AbstractVector{<:Atom})
    out = Dict{Target,Vector{Tuple{Atom,AbstractEffect}}}()
    for a in atoms, (t, e) in expand(a)
        push!(get!(out, t, Tuple{Atom,AbstractEffect}[]), (a, e))
    end
    return out
end

# -------------------------------------------------------------- conflicts ---

"""
    Conflict

A same-target overlap that the target's algebra cannot combine. `required` is
an algebra that would resolve it.
"""
struct Conflict
    target::Target
    overlap::AbstractSupport
    left::Atom
    right::Atom
    reason::String
    required::Union{Nothing,AbstractAlgebra}
end

function Base.show(io::IO, c::Conflict)
    print(io, "Conflict(", c.target, " on ", c.overlap, ": ", c.left.id, " vs ", c.right.id,
          "; ", c.reason)
    c.required === nothing || print(io, "; declare ", c.required)
    print(io, ")")
end

struct InterventionConflictError <: Exception
    conflicts::Vector{Conflict}
end

@doc """
    InterventionConflictError(conflicts)

Thrown when a program has unresolved conflicts. Inspect `.conflicts`.
""" InterventionConflictError

function Base.showerror(io::IO, err::InterventionConflictError)
    println(io, "Intervention program has $(length(err.conflicts)) conflict(s):")
    for c in err.conflicts
        println(io, "  - ", c)
    end
end

"""
    conflicts(program) -> Vector{Conflict}

All pairs of atoms that overlap in time, touch the same target, and whose
effects the target's algebra cannot combine. For the shipped PCMs, pairwise
combinability is equivalent to conflict-freeness (Lean:
`conflictFree_of_pairwise`).
"""
function conflicts(p::Program)
    out = Conflict[]
    n = length(p.atoms)
    for i in 1:n, j in (i + 1):n
        a, b = p.atoms[i], p.atoms[j]
        ov = intersection(a.support, b.support)
        ov === nothing && continue
        ea, eb = Dict(expand(a)), Dict(expand(b))
        for t in intersect(keys(ea), keys(eb))
            alg = algebra(p, t)
            alg isa AbstractOrderedPolicy && continue
            combine(alg, ea[t], eb[t]) === nothing || continue
            push!(out, Conflict(t, ov, a, b,
                                "effects $(ea[t]) and $(eb[t]) do not combine under $(alg)",
                                required_algebra(ea[t], eb[t])))
        end
    end
    return out
end

"""
    validate(program) -> Bool

`true` when the program has no conflicts.
"""
validate(p::Program) = isempty(conflicts(p))

function check_conflicts(p::Program)
    cs = conflicts(p)
    isempty(cs) || throw(InterventionConflictError(cs))
    return p
end

# ------------------------------------------------------------ composition ---

"""
    compose(programs...; check=true)
    p ⊕ q

Compose programs: concatenate atoms and merge declaration tables. With
`check=true` a conflicting composite throws `InterventionConflictError`.
Associative with the empty program as identity (Lean: `compose_assoc`).
"""
function compose(programs::Program...; check::Bool=true)
    atoms = reduce(vcat, (p.atoms for p in programs); init=Atom[])
    space = reduce(merge, (p.space for p in programs); init=TargetSpace())
    out = Program(atoms, space)
    check && check_conflicts(out)
    return out
end
compose(p::Program, a::Atom; kw...) = compose(p, Program(a; space=p.space); kw...)
compose(a::Atom, p::Program; kw...) = compose(Program(a; space=p.space), p; kw...)
compose(a::Atom, b::Atom; kw...) = compose(Program(a), Program(b); kw...)

const compose_interventions = compose

"""
    restrict(program, lo, hi) -> Program

The atoms meeting the closed window `[lo, hi]`, with spans clipped to
`[lo, hi)`. The `restrict` operation of the design note.
"""
function restrict(p::Program, lo, hi)
    atoms = Atom[]
    for a in p.atoms
        meets_closed(a.support, lo, hi) || continue
        if a.support isa Span
            slo, shi = max(a.support.lo, lo), min(a.support.hi, hi)
            slo < shi || continue
            push!(atoms, Atom(a.id, a.target, Span(slo, shi), a.effect, a.metadata))
        else
            push!(atoms, a)
        end
    end
    return Program(atoms, p.space)
end

# ----------------------------------------------------------------- epochs ---

"""
    Epoch

A maximal span on which the set of active span atoms is constant. Records the
active atoms, their combined effect per target (`nothing` where the algebra
fails), and the pulses that fall inside the span.
"""
struct Epoch
    support::Span
    atoms::Vector{Atom}
    effects::Dict{Target,Union{Nothing,AbstractEffect}}
    pulses::Vector{Atom}
end

Base.show(io::IO, e::Epoch) = print(io, "Epoch(", e.support, ", targets=", collect(keys(e.effects)), ")")

function _fold_all(p::Program, atoms::AbstractVector{<:Atom})
    out = Dict{Target,Union{Nothing,AbstractEffect}}()
    for (t, contribs) in contributions(atoms)
        out[t] = fold(algebra(p, t), contribs)[1]
    end
    return out
end

boundaries(p::Program) = sort!(unique!([b for a in p.atoms if a.support isa Span for b in endpoints(a.support)]))

"""
    epochs(program; check=true) -> Vector{Epoch}

The common refinement of all span supports. Adding atoms only refines this
partition (Lean: `epochs_refine`). With `check=false`, conflicting targets are
recorded with effect `nothing` instead of throwing.
"""
function epochs(p::Program; check::Bool=true)
    check && check_conflicts(p)
    bs = boundaries(p)
    out = Epoch[]
    for i in 1:(length(bs) - 1)
        s = Span(bs[i], bs[i + 1])
        act = Atom[a for a in p.atoms if a.support isa Span && overlaps(a.support, s)]
        isempty(act) && continue
        pulses = Atom[a for a in p.atoms if a.support isa Instant && a.support.t ∈ s]
        push!(out, Epoch(s, act, _fold_all(p, act), pulses))
    end
    return out
end
const epochize = epochs

"""
    active_effects(program, t; check=true) -> Dict{Target, effect}

Combined effect per target at time `t`, over all active atoms (spans and
instants).
"""
function active_effects(p::Program, t; check::Bool=true)
    check && check_conflicts(p)
    return _fold_all(p, active(p, t))
end
