"""
Supports: where in time an intervention acts.

A [`Span`](@ref) is a half-open interval `[lo, hi)`; an [`Instant`](@ref) is a
single time point. Both are convex subsets of the timeline, which is the only
property the theory needs (Lean: `support_ordConnected`).
"""

abstract type AbstractSupport{T} end

"""
    Span(lo, hi)
    lo .. hi

Half-open support `[lo, hi)` with `lo < hi`. The start time is included and the
stop time excluded, so adjacent spans partition time. Type `\\bbI<TAB>` for the
`𝕀` alias.
"""
struct Span{T} <: AbstractSupport{T}
    lo::T
    hi::T
    function Span{T}(lo::T, hi::T) where {T}
        lo < hi || throw(ArgumentError("Span requires lo < hi; got [$lo, $hi)"))
        new{T}(lo, hi)
    end
end

Span(lo::T, hi::T) where {T} = Span{T}(lo, hi)
Span(lo, hi) = Span(promote(lo, hi)...)
Span(t::Tuple) = Span(t[1], t[2])

"""
    Instant(t)

A single time point. Used for state pulses, which act at an instant rather than
over an interval.
"""
struct Instant{T} <: AbstractSupport{T}
    t::T
end

"""
    lo .. hi

The span `[lo, hi)`; the same as `Span(lo, hi)`.
"""
const (..) = Span

"""
    Interval(start, stop)

Deprecated alias for [`Span`](@ref), kept for v0.1 compatibility.
"""
Interval(start, stop) = Span(start, stop)

Base.show(io::IO, s::Span) = print(io, "[", s.lo, ", ", s.hi, ")")
Base.show(io::IO, s::Instant) = print(io, "{", s.t, "}")

Base.:(==)(a::Span, b::Span) = a.lo == b.lo && a.hi == b.hi
Base.:(==)(a::Instant, b::Instant) = a.t == b.t
Base.hash(s::Span, h::UInt) = hash((:span, s.lo, s.hi), h)
Base.hash(s::Instant, h::UInt) = hash((:instant, s.t), h)

"""
    contains_time(support, t) -> Bool
    t ∈ support

Is `t` in the support?
"""
contains_time(s::Span, t) = s.lo <= t < s.hi
contains_time(s::Instant, t) = s.t == t
Base.in(t, s::AbstractSupport) = contains_time(s, t)

"""
    overlaps(a, b) -> Bool

Do two supports share a time?
"""
overlaps(a::Span, b::Span) = a.lo < b.hi && b.lo < a.hi
overlaps(a::Span, b::Instant) = contains_time(a, b.t)
overlaps(a::Instant, b::Span) = overlaps(b, a)
overlaps(a::Instant, b::Instant) = a.t == b.t
isdisjoint(a::AbstractSupport, b::AbstractSupport) = !overlaps(a, b)

"""
    intersection(a, b) -> support or nothing

The common part of two supports, or `nothing` if they are disjoint.
"""
function intersection(a::Span, b::Span)
    overlaps(a, b) || return nothing
    return Span(max(a.lo, b.lo), min(a.hi, b.hi))
end
intersection(a::Span, b::Instant) = overlaps(a, b) ? b : nothing
intersection(a::Instant, b::Span) = intersection(b, a)
intersection(a::Instant, b::Instant) = a == b ? a : nothing
Base.intersect(a::AbstractSupport, b::AbstractSupport) = intersection(a, b)

"""
    meets_closed(s, lo, hi) -> Bool

Does the support meet the closed interval `[lo, hi]`?  Used by the cumulative
narrative.
"""
meets_closed(s::Span, lo, hi) = s.lo <= hi && lo < s.hi
meets_closed(s::Instant, lo, hi) = lo <= s.t <= hi

"""
    covers_closed(s, lo, hi) -> Bool

Does the support contain the whole closed interval `[lo, hi]`?  Used by the
persistent narrative.
"""
covers_closed(s::Span, lo, hi) = s.lo <= lo && hi < s.hi
covers_closed(s::Instant, lo, hi) = lo == hi == s.t

"""
    shift(support, δ)

Translate a support later in time by `δ`.
"""
shift(s::Span, δ) = Span(s.lo + δ, s.hi + δ)
shift(s::Instant, δ) = Instant(s.t + δ)

"""
    endpoints(support)

The event times of a support: `(lo, hi)` for a span, `(t,)` for an instant.
"""
endpoints(s::Span) = (s.lo, s.hi)
endpoints(s::Instant) = (s.t,)
isspan(::Span) = true
isspan(::Instant) = false
