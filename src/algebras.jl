"""
Effects and the algebras that combine them.

An effect is a local edit to a value. An algebra says what two effects on the
same target at the same time mean together. Partial commutative monoids (PCMs)
give order-independent composition that may be undefined; ordered policies
resolve overlaps by program order or priority and are explicitly
order-dependent.
"""

# ---------------------------------------------------------------- effects ---

abstract type AbstractEffect end

"""
    Identity()

The effect that does nothing. It is the unit of every algebra.
"""
struct Identity <: AbstractEffect end

"""
    SetValue(value)

Absolute effect: replace the target value with `value`.
"""
struct SetValue{T} <: AbstractEffect
    value::T
end

"""
    Add(delta)

Additive effect: `x ↦ x + delta`.
"""
struct Add{T} <: AbstractEffect
    delta::T
end

"""
    Scale(factor)

Multiplicative effect: `x ↦ x * factor`.
"""
struct Scale{T} <: AbstractEffect
    factor::T
end

"""
    CapAt(limit)

Upper-bound effect: `x ↦ min(x, limit)`.
"""
struct CapAt{T} <: AbstractEffect
    limit::T
end

"""
    FloorAt(limit)

Lower-bound effect: `x ↦ max(x, limit)`.
"""
struct FloorAt{T} <: AbstractEffect
    limit::T
end

"""
    MapEffect(f, label=:custom)

Custom effect given by an explicit function. Combines only under `Reject` (as
the sole effect) or an ordered policy.
"""
struct MapEffect{F} <: AbstractEffect
    f::F
    label::Symbol
end
MapEffect(f) = MapEffect(f, :custom)

"""
    AffineEffect(absolute, relative)

Normal form of the [`Affine`](@ref) algebra: an optional absolute assignment
followed by a relative effect. Means "set to `absolute` (if present), then apply
`relative`".
"""
struct AffineEffect{A,R<:AbstractEffect} <: AbstractEffect
    absolute::A          # ::Union{Nothing, SetValue}
    relative::R
end

"""
    Transfer(to, amount)

State pulse that moves `amount` from the atom's target state to the state named
`to`. A single atom that conserves the total by construction.
"""
struct Transfer{T} <: AbstractEffect
    to::Symbol
    amount::T
end

"""
    Flow(to, rate)

State flow: a continuous transfer from the atom's target state to `to` at
per-capita `rate` over the atom's span. Realised by [`augment`](@ref), which
turns it into a parameter interval on an augmented model.
"""
struct Flow{T} <: AbstractEffect
    to::Symbol
    rate::T
end

apply_effect(::Identity, v) = v
apply_effect(e::SetValue, v) = e.value
apply_effect(e::Add, v) = v + e.delta
apply_effect(e::Scale, v) = v * e.factor
apply_effect(e::CapAt, v) = min(v, e.limit)
apply_effect(e::FloorAt, v) = max(v, e.limit)
apply_effect(e::MapEffect, v) = e.f(v)
apply_effect(e::AffineEffect, v) =
    apply_effect(e.relative, e.absolute === nothing ? v : e.absolute.value)
apply_effect(e::Transfer, v) = v - e.amount
apply_effect(::Flow, v) = v

effect_mode(::Identity) = :identity
effect_mode(::SetValue) = :absolute
effect_mode(::Add) = :additive
effect_mode(::Scale) = :multiplicative
effect_mode(::CapAt) = :cap
effect_mode(::FloorAt) = :floor
effect_mode(e::MapEffect) = e.label
effect_mode(::AffineEffect) = :affine
effect_mode(::Transfer) = :transfer
effect_mode(::Flow) = :flow

Base.show(io::IO, ::Identity) = print(io, "id")
Base.show(io::IO, e::SetValue) = print(io, "set(", e.value, ")")
Base.show(io::IO, e::Add) = print(io, "add(", e.delta, ")")
Base.show(io::IO, e::Scale) = print(io, "scale(", e.factor, ")")
Base.show(io::IO, e::CapAt) = print(io, "cap(", e.limit, ")")
Base.show(io::IO, e::FloorAt) = print(io, "floor(", e.limit, ")")
Base.show(io::IO, e::MapEffect) = print(io, "map(", e.label, ")")
Base.show(io::IO, e::Transfer) = print(io, "transfer(", e.amount, " → ", e.to, ")")
Base.show(io::IO, e::Flow) = print(io, "flow(rate ", e.rate, " → ", e.to, ")")
function Base.show(io::IO, e::AffineEffect)
    if e.absolute === nothing
        show(io, e.relative)
    else
        show(io, e.absolute)
        e.relative isa Identity || (print(io, " then "); show(io, e.relative))
    end
end

# --------------------------------------------------------------- algebras ---

abstract type AbstractAlgebra end
"""Partial commutative monoids: order-independent, possibly undefined combination."""
abstract type AbstractPCM <: AbstractAlgebra end
"""Ordered policies: total but order-dependent combination."""
abstract type AbstractOrderedPolicy <: AbstractAlgebra end

"""
    Reject()

Default algebra. Two overlapping effects on the same target are a conflict
unless one of them is the identity.
"""
struct Reject <: AbstractPCM end

"""
    Multiplicative()

Overlapping `Scale` effects multiply.
"""
struct Multiplicative <: AbstractPCM end

"""
    Additive()

Overlapping `Add` (and `Transfer`) effects add.
"""
struct Additive <: AbstractPCM end

"""
    Cap()

Overlapping `CapAt` effects take the tighter limit (`min`).
"""
struct Cap <: AbstractPCM end

"""
    Floor()

Overlapping `FloorAt` effects take the tighter limit (`max`).
"""
struct Floor <: AbstractPCM end

"""
    Affine(relative::AbstractPCM)

At most one absolute `SetValue`, combined with any number of relative effects
from `relative`; means "set, then apply the relative effects". Two overlapping
absolute assignments are a conflict. This is the default for rates in models
built from AlgebraicPetri and StockFlow.
"""
struct Affine{M<:AbstractPCM} <: AbstractPCM
    relative::M
end

"""
    LatestWins()

Ordered policy: the later atom in program order replaces the earlier one.
"""
struct LatestWins <: AbstractOrderedPolicy end

"""
    HighestPriority()

Ordered policy: the atom with the largest `metadata[:priority]` wins; ties go to
the later atom in program order.
"""
struct HighestPriority <: AbstractOrderedPolicy end

Base.show(io::IO, a::Affine) = print(io, "Affine(", a.relative, ")")

"""
    combine(algebra, e1, e2) -> effect or nothing

The partial product of a PCM. `nothing` means the pair does not combine.
"""
combine(::AbstractPCM, ::Identity, e::AbstractEffect) = e
combine(::AbstractPCM, e::AbstractEffect, ::Identity) = e
combine(::AbstractPCM, ::Identity, ::Identity) = Identity()
combine(::AbstractPCM, ::AbstractEffect, ::AbstractEffect) = nothing

combine(::Multiplicative, a::Scale, b::Scale) = Scale(a.factor * b.factor)
combine(::Additive, a::Add, b::Add) = Add(a.delta + b.delta)
combine(::Additive, a::Transfer, b::Add) = Add(-a.amount + b.delta)
combine(::Additive, a::Add, b::Transfer) = Add(a.delta - b.amount)
combine(::Additive, a::Transfer, b::Transfer) = Add(-a.amount - b.amount)
combine(::Cap, a::CapAt, b::CapAt) = CapAt(min(a.limit, b.limit))
combine(::Floor, a::FloorAt, b::FloorAt) = FloorAt(max(a.limit, b.limit))

_affine(e::AffineEffect) = e
_affine(e::SetValue) = AffineEffect(e, Identity())
_affine(e::AbstractEffect) = AffineEffect(nothing, e)

combine(::Affine, ::Identity, e::AbstractEffect) = e
combine(::Affine, e::AbstractEffect, ::Identity) = e
combine(::Affine, ::Identity, ::Identity) = Identity()
function combine(alg::Affine, a::AbstractEffect, b::AbstractEffect)
    x, y = _affine(a), _affine(b)
    x.absolute !== nothing && y.absolute !== nothing && return nothing
    rel = combine(alg.relative, x.relative, y.relative)
    rel === nothing && return nothing
    return AffineEffect(x.absolute === nothing ? y.absolute : x.absolute, rel)
end

"""
    required_algebra(e1, e2) -> algebra or nothing

The algebra that would make two effects combine, for conflict reports.
"""
required_algebra(::Scale, ::Scale) = Multiplicative()
required_algebra(::Union{Add,Transfer}, ::Union{Add,Transfer}) = Additive()
required_algebra(::CapAt, ::CapAt) = Cap()
required_algebra(::FloorAt, ::FloorAt) = Floor()
required_algebra(::SetValue, ::Scale) = Affine(Multiplicative())
required_algebra(::Scale, ::SetValue) = Affine(Multiplicative())
required_algebra(::SetValue, ::Add) = Affine(Additive())
required_algebra(::Add, ::SetValue) = Affine(Additive())
required_algebra(::SetValue, ::SetValue) = LatestWins()
required_algebra(::AbstractEffect, ::AbstractEffect) = LatestWins()

# Ordered policies pick an atom rather than combining effects; see programs.jl.
