module CategoricalInterventionsAlgebraicPetriExt

using AlgebraicPetri
using AlgebraicPetri: LabelledPetriNetUntyped
using Catlab
using Catlab.CategoricalAlgebra: ACSetTransformation, dom, codom, components, ACSetCategory, pullback, apex, legs
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    PetriMorphism(dom, codom, S, T)

A morphism of labelled Petri nets recorded by its species and transition
components (1-based index vectors). Produced by [`stratify`](@ref) and accepted
wherever an `ACSetTransformation` is.
"""
struct PetriMorphism
    dom::AbstractLabelledPetriNet
    codom::AbstractLabelledPetriNet
    S::Vector{Int}
    T::Vector{Int}
end
Base.show(io::IO, m::PetriMorphism) = print(io, "PetriMorphism(", ns(m.dom), "→", ns(m.codom), " species, ",
                                            nt(m.dom), "→", nt(m.codom), " transitions)")
CI.dom(m::PetriMorphism) = m.dom
CI.codom(m::PetriMorphism) = m.codom
_S(m::PetriMorphism, s) = m.S[s]
_T(m::PetriMorphism, t) = m.T[t]
_S(m::ACSetTransformation, s) = m[:S](s)
_T(m::ACSetTransformation, t) = m[:T](t)
_dom(m::PetriMorphism) = m.dom
_codom(m::PetriMorphism) = m.codom
_dom(m::ACSetTransformation) = dom(m)
_codom(m::ACSetTransformation) = codom(m)
const AnyPetriMorphism = Union{PetriMorphism,ACSetTransformation}

_untype(lpn::AbstractPetriNet) = (p = PetriNet(); copy_parts!(p, lpn); p)

"""
    typed_by(net, types, transition_types::Dict) -> ACSetTransformation

Type an (untyped copy of a) labelled net by a type system: every species maps
to the single species of `types`, and each transition to the type named for
it. Input and output arcs are matched positionally within each transition.
"""
function CI.typed_by(net::AbstractLabelledPetriNet, types::AbstractLabelledPetriNet, transition_types::AbstractDict)
    u, ut = _untype(net), _untype(types)
    ns(types) == 1 || error("typed_by assumes a single species type")
    tmap = [findfirst(==(transition_types[_label(tname(net, t))]), _transition_labels(types)) for t in 1:nt(net)]
    any(isnothing, tmap) && error("every transition needs a type in `transition_types`")
    I = zeros(Int, ni(u)); O = zeros(Int, no(u))
    for t in 1:nt(u)
        tt = tmap[t]
        ins, outs = incident(ut, tt, :it), incident(ut, tt, :ot)
        for (k, i) in enumerate(incident(u, t, :it))
            k <= length(ins) || error("transition $(tname(net, t)) has more inputs than its type")
            I[i] = ins[k]
        end
        for (k, o) in enumerate(incident(u, t, :ot))
            k <= length(outs) || error("transition $(tname(net, t)) has more outputs than its type")
            O[o] = outs[k]
        end
    end
    return ACSetTransformation(u, ut; S=fill(1, ns(u)), T=tmap, I=I, O=O)
end

"""
    stratify(base, strata, types, base_types, strata_types) -> (net, to_base, to_strata)

Stratify `base` by `strata` over a one-species type system `types`: the
pullback of the two typing maps. Species of the result are labelled
`(base_species, stratum)` and transitions `(base_transition, stratum_transition)`.
`to_base` and `to_strata` are the projections, usable with `lift` and
`pushforward`. Reflexive "stay in place" transitions must already be present
in each net wherever the other net's transitions should apply (as in
AlgebraicPetri's `add_reflexives`).
"""
function CI.stratify(base::AbstractLabelledPetriNet, strata::AbstractLabelledPetriNet, types::AbstractLabelledPetriNet,
                     base_types::AbstractDict, strata_types::AbstractDict)
    f = CI.typed_by(base, types, base_types)
    g = CI.typed_by(strata, types, strata_types)
    pb = pullback[ACSetCategory(codom(f))](f, g)
    X = apex(pb); l1, l2 = legs(pb)
    net = LabelledPetriNetUntyped{Tuple{Symbol,Symbol}}()
    add_parts!(net, :S, ns(X); sname=[(sname(base, l1[:S](s)), sname(strata, l2[:S](s))) for s in 1:ns(X)])
    add_parts!(net, :T, nt(X); tname=[(tname(base, l1[:T](t)), tname(strata, l2[:T](t))) for t in 1:nt(X)])
    add_parts!(net, :I, ni(X); it=X[:, :it], is=X[:, :is])
    add_parts!(net, :O, no(X); ot=X[:, :ot], os=X[:, :os])
    return (net=net, to_base=PetriMorphism(net, base, collect(l1[:S]), collect(l1[:T])),
            to_strata=PetriMorphism(net, strata, collect(l2[:S]), collect(l2[:T])))
end

_label(x::Symbol) = x
_label(x::AbstractString) = Symbol(x)
_label(x::Tuple) = Symbol(join(string.(x), "_"))
_label(x) = Symbol(string(x))

_species_labels(pn) = [_label(sname(pn, s)) for s in 1:ns(pn)]
_transition_labels(pn) = [_label(tname(pn, t)) for t in 1:nt(pn)]

"""
    conserves_tokens(pn)

Every transition has as many inputs as outputs, so mass action conserves the
total population.
"""
CI.conserves_tokens(pn::AbstractPetriNet) = all(t -> length(inputs(pn, t)) == length(outputs(pn, t)), 1:nt(pn))

"""
    Model(pn::AbstractLabelledPetriNet; kind=:continuous, invariants=nothing, ...)

A model whose rates are the net's transitions (set-then-scale algebra) and
whose states are its species (additive algebra). Tuple labels from a product
net are flattened with `_`. A conservation invariant is added automatically
when every transition conserves tokens.
"""
function CI.Model(pn::AbstractLabelledPetriNet; kind::Symbol=:continuous, invariants=nothing,
                  rate_algebra=Affine(Multiplicative()), state_algebra=Additive(), value_type::Type=Float64)
    flat = all(x -> x isa Symbol, snames(pn)) && all(x -> x isa Symbol, tnames(pn)) ? pn : flatten_labels(pn)
    sn, tn = _species_labels(flat), _transition_labels(flat)
    inv = invariants === nothing ? (CI.conserves_tokens(flat) ? [Conserved(sn)] : CI.AbstractInvariant[]) : invariants
    return Model(vectorfield(flat); parameters=tn, states=sn, kind, invariants=inv, rate_algebra, state_algebra,
                 value_type, metadata=Dict{Symbol,Any}(:petri => flat, :original => pn, :source => :AlgebraicPetri))
end

"""
    target_map(m::ACSetTransformation) -> Dict{Target,Target}

The map of targets induced by a Petri-net morphism: species to state targets,
transitions to parameter targets.
"""
function CI.target_map(m::AnyPetriMorphism)
    d, c = _dom(m), _codom(m)
    out = Dict{Target,Target}()
    for s in 1:ns(d)
        out[Target(_label(sname(d, s)), State)] = Target(_label(sname(c, _S(m, s))), State)
    end
    for t in 1:nt(d)
        out[Target(_label(tname(d, t)), Parameter)] = Target(_label(tname(c, _T(m, t))), Parameter)
    end
    return out
end

"""
    strata(pn) -> Dict{Target,Any}

For a product net with tuple labels `(base, stratum)`, the stratum of each
species target; used by `lift` to match transfer destinations.
"""
function CI.strata(pn::AbstractLabelledPetriNet)
    out = Dict{Target,Any}()
    for s in 1:ns(pn)
        l = sname(pn, s)
        l isa Tuple && length(l) >= 2 && (out[Target(_label(l), State)] = l[2])
    end
    return out
end

CI.pushforward(p::Program, m::AnyPetriMorphism; kw...) = CI.pushforward(p, CI.target_map(m); kw...)

"""
    lift(program, π; space=nothing)

Pull a program back along a projection from a stratified net to its base net
(a `PetriMorphism` from `stratify` or an `ACSetTransformation`). Strata are
read from the tuple labels of the domain.
"""
function CI.lift(p::Program, π::AnyPetriMorphism; kw...)
    CI.lift(p, CI.target_map(π); strata=CI.strata(_dom(π)), kw...)
end

"""
    augment_flow(model, from, to, rate_name)

Add a transition `from → to` named `rate_name` to the model's Petri net.
"""
function CI.augment_flow(m::Model, from::Symbol, to::Symbol, rate_name::Symbol)
    haskey(m.metadata, :petri) || error("augment_flow needs a model built from an AlgebraicPetri net")
    pn = copy(m.metadata[:petri])
    s_from = findfirst(==(from), _species_labels(pn)); s_to = findfirst(==(to), _species_labels(pn))
    (s_from === nothing || s_to === nothing) && error("Flow endpoints $from → $to are not species of the net")
    t = add_transition!(pn; tname=rate_name)
    add_input!(pn, t, s_from)
    add_output!(pn, t, s_to)
    model = Model(pn; kind=m.kind, invariants=m.invariants)
    for (target, s) in m.space.specs
        model.space.specs[target] = s
    end
    return model
end

end # module
