"""
The plain API: intervention constructors that read like the policy they
describe, and the `@interventions` block.

    scale(:inf, 0.5; during=5..25)          # multiply a rate on a span
    set(:gamma, 0.25; during=20..40)        # assign a rate on a span
    add(:I, 5; at=20)                       # add to a state at an instant
    transfer(:S => :R, 50; at=15)           # move between states at an instant
    flow(:S => :R; rate=0.01, during=30..60) # continuous transfer on a span
    cap(:contacts, 5; during=0..10)         # upper bound
    floor_at(:testing, 100; during=0..10)   # lower bound
    custom(:beta, x -> x^2; during=0..10)   # any function

Kinds are inferred: `at=` means a state pulse, `during=` a parameter interval,
except for `transfer` and `flow` which are always on states. Pass a `Target`
to be explicit.
"""

_support(s::AbstractSupport) = s
_support(t::Tuple) = Span(t[1], t[2])
_support(r::AbstractRange) = Span(first(r), last(r))

const _counter = Ref(0)
function _auto_id(prefix, name)
    _counter[] += 1
    return Symbol(prefix, "_", name, "_", _counter[])
end

_target(t::Target, ::TargetKind) = t
_target(name::Symbol, kind::TargetKind) = Target(name, kind)
_target(name::AbstractString, kind::TargetKind) = Target(Symbol(name), kind)

function _where(; during=nothing, at=nothing)
    (during === nothing) == (at === nothing) &&
        throw(ArgumentError("give exactly one of `during=lo..hi` or `at=t`"))
    return during === nothing ? Instant(at) : _support(during)
end

function _make(prefix, target, effect; during=nothing, at=nothing, id=nothing,
               kind::Union{Nothing,TargetKind}=nothing, metadata=Dict{Symbol,Any}())
    support = _where(; during, at)
    k = kind !== nothing ? kind : (support isa Instant ? State : Parameter)
    t = _target(target, k)
    name = id === nothing ? _auto_id(prefix, t.name) : id
    return Atom(name, t, support, effect, Dict{Symbol,Any}(metadata))
end

"""
    scale(target, factor; during, id, kind, metadata)

Multiply a parameter by `factor` on a span.
"""
scale(target, factor; kw...) = _make(:scale, target, Scale(factor); kw...)

"""
    set(target, value; during | at, id, kind, metadata)

Assign a value on a span (parameters) or at an instant (states).
"""
set(target, value; kw...) = _make(:set, target, SetValue(value); kw...)

"""
    add(target, delta; during | at, id, kind, metadata)

Add `delta` on a span (parameters) or at an instant (states).
"""
add(target, delta; kw...) = _make(:add, target, Add(delta); kw...)

"""
    cap(target, limit; during, id, kind, metadata)

Bound a parameter above by `limit` on a span.
"""
cap(target, limit; kw...) = _make(:cap, target, CapAt(limit); kw...)

"""
    floor_at(target, limit; during, id, kind, metadata)

Bound a parameter below by `limit` on a span.
"""
floor_at(target, limit; kw...) = _make(:floor, target, FloorAt(limit); kw...)

"""
    custom(target, f; during | at, label=:custom, id, kind, metadata)

Apply an arbitrary function to the value.
"""
custom(target, f; label::Symbol=:custom, kw...) = _make(:custom, target, MapEffect(f, label); kw...)

"""
    transfer(from => to, amount; at, id, metadata)

Move `amount` from state `from` to state `to` at an instant. One atom;
conserves the total by construction.
"""
function transfer(pair::Pair, amount; at, id=nothing, metadata=Dict{Symbol,Any}())
    from, to = pair
    t = _target(from, State)
    name = id === nothing ? _auto_id(:transfer, Symbol(t.name, "_", Symbol(to))) : id
    return Atom(name, t, Instant(at), Transfer(Symbol(to), amount), Dict{Symbol,Any}(metadata))
end

"""
    flow(from => to; rate, during, id, metadata)

A continuous per-capita transfer from `from` to `to` on a span. Realised by
[`augment`](@ref).
"""
function flow(pair::Pair; rate, during, id=nothing, metadata=Dict{Symbol,Any}())
    from, to = pair
    t = _target(from, State)
    name = id === nothing ? _auto_id(:flow, Symbol(t.name, "_", Symbol(to))) : id
    return Atom(name, t, _support(during), Flow(Symbol(to), rate), Dict{Symbol,Any}(metadata))
end

_space_of(m::Model) = m.space
_space_of(s::TargetSpace) = s
_space_of(p::Program) = p.space

"""
    @interventions model begin
        lockdown    = scale(:inf, 0.5; during=5..25)
        vaccination = transfer(:S => :R, 50; at=15)
    end

Build a `Program` on the model's targets, using each assignment's name as the
atom id. `model` may be a `Model`, a `TargetSpace`, or another `Program`.
Bare expressions (no `name =`) get automatic ids.
"""
macro interventions(model, block)
    block isa Expr && block.head == :block || error("@interventions expects a begin ... end block")
    atoms = Any[]
    for line in block.args
        line isa LineNumberNode && continue
        if line isa Expr && line.head == :(=) && line.args[1] isa Symbol
            id, call = line.args
            push!(atoms, _with_id(call, id))
        else
            push!(atoms, line)
        end
    end
    return esc(:($Program([$(atoms...)]; space=$_space_of($model))))
end

function _with_id(call, id)
    call isa Expr && call.head == :call || error("@interventions: `$id = ...` must be a constructor call")
    kw = Expr(:kw, :id, QuoteNode(id))
    if length(call.args) >= 2 && call.args[2] isa Expr && call.args[2].head == :parameters
        push!(call.args[2].args, kw)
    else
        insert!(call.args, 2, Expr(:parameters, kw))
    end
    return call
end
