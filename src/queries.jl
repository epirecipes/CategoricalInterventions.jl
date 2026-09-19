"""
Temporal queries on programs via Catlab subobjects.

A discrete narrative on a window `t₁ < … < tₙ` is a graph over the path graph
(Niu et al., Cor. 2.7): vertices are "target `j` is under intervention at
`tₖ`", edges are "target `j` is under intervention throughout `[tₖ, tₖ₊₁]`".
The ambient [`NarrativeWindow`](@ref) has every such vertex and edge for the
targets in view; a program picks out a subobject, and Catlab's subobject
lattice supplies meet, join, negation and Heyting implication.

Because a program's persistent narrative satisfies the sheaf equation (Lean:
`persistent_glue`), the edge for `[tₖ, tₖ₊₁]` is present exactly when the
target is covered by a single atom throughout, so the five truth values of the
paper's subobject classifier on a unit interval are read off the pair of
vertices and the edge.
"""

using Catlab.Graphs: Graph, add_vertices!, add_edges!, nv, ne
using Catlab.CategoricalAlgebra: Subobject, components, predicate, force
import Catlab.CategoricalAlgebra: implies, meet, join, negate, ⟹, ∧, ∨, ¬

# Catlab ≥ 0.16 dispatches the Heyting operations through an explicit category
# model; earlier versions dispatch on the subobjects directly.
const _ACSetCategory = isdefined(Catlab.CategoricalAlgebra, :ACSetCategory) ?
                       getproperty(Catlab.CategoricalAlgebra, :ACSetCategory) : nothing
_category(g) = _ACSetCategory === nothing ? nothing : _ACSetCategory(g)
_with(op, cat, args...) = cat === nothing ? op(args...) : op[cat](args...)

"""
    NarrativeWindow(targets, times)

The ambient graph of a finite window: one vertex per `(target, time)` and one
edge per `(target, unit interval)`.
"""
struct NarrativeWindow
    targets::Vector{Target}
    times::Vector
    graph::Graph
    vertex::Dict{Tuple{Target,Int},Int}
    edge::Dict{Tuple{Target,Int},Int}
    category::Any   # Catlab ACSetCategory, the model for the Heyting operations
end

function NarrativeWindow(targets::AbstractVector{Target}, times::AbstractVector)
    ts = collect(times)
    n = length(ts)
    g = Graph()
    vertex = Dict{Tuple{Target,Int},Int}()
    edge = Dict{Tuple{Target,Int},Int}()
    for j in targets
        vs = add_vertices!(g, n)
        for (k, v) in enumerate(vs)
            vertex[(j, k)] = v
        end
        es = add_edges!(g, vs[1:end-1], vs[2:end])
        for (k, e) in enumerate(es)
            edge[(j, k)] = e
        end
    end
    return NarrativeWindow(collect(targets), ts, g, vertex, edge, _category(g))
end

Base.show(io::IO, w::NarrativeWindow) =
    print(io, "NarrativeWindow(", length(w.targets), " targets × ", length(w.times), " times)")

"""
    NarrativeSubobject

A program (or query result) as a subobject of a window's graph.
"""
struct NarrativeSubobject
    window::NarrativeWindow
    sub::Any   # Catlab Subobject
end

function _sub(w::NarrativeWindow, V::AbstractVector{Bool}, E::AbstractVector{Bool})
    return NarrativeSubobject(w, Subobject(w.graph, V=V, E=E))
end

"""
    subobject(window, program) -> NarrativeSubobject

The program's target-level persistent narrative on the window: vertex `(j, k)`
iff some atom on `j` is active at `tₖ`; edge `(j, k)` iff some atom on `j`
covers `[tₖ, tₖ₊₁]`.
"""
function subobject(w::NarrativeWindow, p::Program)
    V = falses(nv(w.graph))
    E = falses(ne(w.graph))
    A = persistent(p)
    for j in w.targets
        for k in eachindex(w.times)
            any(a -> j in atom_targets(a), A(w.times[k])) && (V[w.vertex[(j, k)]] = true)
        end
        for k in 1:(length(w.times) - 1)
            any(a -> j in atom_targets(a), A(w.times[k], w.times[k + 1])) && (E[w.edge[(j, k)]] = true)
        end
    end
    return _sub(w, V, E)
end
subobject(w::NarrativeWindow, s::NarrativeSubobject) = s

_V(s::NarrativeSubobject) = predicate(components(force(s.sub))[:V])
_E(s::NarrativeSubobject) = predicate(components(force(s.sub))[:E])

Base.:(==)(a::NarrativeSubobject, b::NarrativeSubobject) = _V(a) == _V(b) && _E(a) == _E(b)

for (op, name) in ((:meet, :∧), (:join, :∨), (:implies, :⟹))
    @eval begin
        function $op(a::NarrativeSubobject, b::NarrativeSubobject)
            a.window === b.window || error("subobjects live on different windows")
            NarrativeSubobject(a.window, _with($op, a.window.category, a.sub, b.sub))
        end
        $name(a::NarrativeSubobject, b::NarrativeSubobject) = $op(a, b)
    end
end
negate(a::NarrativeSubobject) = NarrativeSubobject(a.window, _with(negate, a.window.category, a.sub))
¬(a::NarrativeSubobject) = negate(a)

"""
    at(sub, target, k) -> Bool
    throughout(sub, target, k) -> Bool

Is the target under intervention at time `tₖ`, or throughout `[tₖ, tₖ₊₁]`?
"""
at(s::NarrativeSubobject, j::Target, k::Integer) = _V(s)[s.window.vertex[(j, k)]]
throughout(s::NarrativeSubobject, j::Target, k::Integer) = _E(s)[s.window.edge[(j, k)]]

"""
    sometime(sub, target, k) -> Bool

Is the target under intervention at some time in `[tₖ, tₖ₊₁]`? For the
subobject of a program this is the cumulative narrative on the unit interval;
it is read off the window at the resolution of the grid (either endpoint, or the
edge).
"""
sometime(s::NarrativeSubobject, j::Target, k::Integer) =
    at(s, j, k) || at(s, j, k + 1) || throughout(s, j, k)

"""
    truth_value(sub, target, k) -> Symbol

The paper's five local truth values on `[tₖ, tₖ₊₁]`: `:false`, `:start_only`,
`:end_only`, `:both_ends_not_throughout`, `:throughout`.
"""
function truth_value(s::NarrativeSubobject, j::Target, k::Integer)
    a, b, e = at(s, j, k), at(s, j, k + 1), throughout(s, j, k)
    e && return :throughout
    a && b && return :both_ends_not_throughout
    a && return :start_only
    b && return :end_only
    return :false
end

const _truth_words = Dict(
    :false => "not in force",
    :start_only => "in force at the start, lifted before the end",
    :end_only => "not in force at the start, in force by the end",
    :both_ends_not_throughout => "in force at both ends but lifted in between",
    :throughout => "in force throughout",
)

"""
    describe(sub; io=stdout)

Print, per target and unit interval, the truth value in words.
"""
function describe(s::NarrativeSubobject; io::IO=stdout)
    w = s.window
    for j in w.targets
        println(io, j.name, ":")
        for k in 1:(length(w.times) - 1)
            println(io, "  [", w.times[k], ", ", w.times[k + 1], "]  ", _truth_words[truth_value(s, j, k)])
        end
    end
end

"""
    throughout(program, target, (lo, hi)) -> Bool
    sometime(program, target, (lo, hi)) -> Bool

Direct narrative queries without a window: is `target` under some atom
throughout the closed interval, or at some time in it?
"""
throughout(p::Program, j::Target, (lo, hi)::Tuple) = any(a -> j in atom_targets(a), persistent(p)(lo, hi))
sometime(p::Program, j::Target, (lo, hi)::Tuple) = any(a -> j in atom_targets(a), cumulative(p)(lo, hi))
throughout(p::Program, name::Symbol, iv::Tuple; kind::TargetKind=Parameter) = throughout(p, Target(name, kind), iv)
sometime(p::Program, name::Symbol, iv::Tuple; kind::TargetKind=Parameter) = sometime(p, Target(name, kind), iv)
