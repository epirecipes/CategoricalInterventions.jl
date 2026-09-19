"""
Models: the target space, indexing, and invariants of a simulation.

A `Model` wraps a dynamics object owned by the host framework (a function, an
AlgebraicPetri vector field, an AlgebraicDynamics system, ...) together with
the declared targets, the selectors that locate each target in the integrator's
`p` and `u`, and the invariants pulses must preserve. Extensions build models
from AlgebraicPetri nets, StockFlow diagrams, and AlgebraicDynamics systems.
"""

# ------------------------------------------------------------- invariants ---

abstract type AbstractInvariant end

"""
    Conserved(states)

The sum of the named states is preserved by every pulse.
"""
struct Conserved <: AbstractInvariant
    states::Vector{Symbol}
end

"""
    Nonnegative(states)

The named states stay non-negative after every pulse.
"""
struct Nonnegative <: AbstractInvariant
    states::Vector{Symbol}
end

Base.:(==)(a::Conserved, b::Conserved) = a.states == b.states
Base.:(==)(a::Nonnegative, b::Nonnegative) = a.states == b.states

"""
    InvariantViolation

Thrown when a pulse breaks one of the model's invariants.
"""
struct InvariantViolation <: Exception
    invariant::AbstractInvariant
    message::String
end
Base.showerror(io::IO, e::InvariantViolation) = print(io, "InvariantViolation: ", e.message)

# --------------------------------------------------------------- indexing ---

_selector(name::Symbol) = name
_selector(name::AbstractString) = Symbol(name)
_selector(index::Integer) = Int(index)
_selector(selector) = selector
_selector_dict(names::AbstractVector) = Dict{Symbol,Any}(Symbol(n) => _selector(n) for n in names)
_selector_dict(names::AbstractDict) = Dict{Symbol,Any}(Symbol(n) => _selector(s) for (n, s) in pairs(names))

"""
    Indexing(; parameters, states)

Selectors locating each target in `integrator.p` and `integrator.u`. A vector of
names uses the names themselves (for labelled arrays); a dictionary maps names
to positions or other selectors. `PetriIndexing` is the v0.1 name.
"""
struct Indexing
    parameters::Dict{Symbol,Any}
    states::Dict{Symbol,Any}
end
Indexing(parameters::Union{AbstractVector,AbstractDict}, states::Union{AbstractVector,AbstractDict}=Symbol[]) =
    Indexing(_selector_dict(parameters), _selector_dict(states))
Indexing(; parameters=Symbol[], states=Symbol[]) = Indexing(parameters, states)
const PetriIndexing = Indexing

# ------------------------------------------------------------------ model ---

"""
    Model(dynamics; parameters, states, kind=:continuous, invariants=[],
          rate_algebra=Affine(Multiplicative()), state_algebra=Additive(),
          value_type=Float64)

A simulation model with declared targets. `parameters` and `states` are vectors
of names (labelled containers) or dictionaries from names to positions.
Rates default to the set-then-scale algebra and states to the additive
algebra.
"""
struct Model{D}
    dynamics::D
    space::TargetSpace
    indexing::Indexing
    invariants::Vector{AbstractInvariant}
    kind::Symbol
    metadata::Dict{Symbol,Any}
end

function Model(dynamics; parameters=Symbol[], states=Symbol[], kind::Symbol=:continuous,
               invariants::AbstractVector=AbstractInvariant[],
               rate_algebra::AbstractAlgebra=Affine(Multiplicative()),
               state_algebra::AbstractAlgebra=Additive(),
               value_type::Type=Float64, metadata=Dict{Symbol,Any}())
    indexing = Indexing(parameters, states)
    space = TargetSpace()
    for name in keys(indexing.parameters)
        declare!(space, Target(name, Parameter), rate_algebra; value_type)
    end
    for name in keys(indexing.states)
        declare!(space, Target(name, State), state_algebra; value_type)
    end
    return Model(dynamics, space, indexing, collect(AbstractInvariant, invariants), kind,
                 Dict{Symbol,Any}(metadata))
end

Base.show(io::IO, m::Model) = print(io, "Model(", length(m.indexing.parameters), " parameters, ",
                                    length(m.indexing.states), " states, ", m.kind, ")")

"""
    parameters(model)

Names of the model's parameter-like targets.
"""
parameters(m::Model) = collect(keys(m.indexing.parameters))

"""
    states(model)

Names of the model's state targets.
"""
states(m::Model) = collect(keys(m.indexing.states))
targets(m::Model) = targets(m.space)

"""
    declare!(model, name, algebra; kind=Parameter, value_type=Float64)

Change the algebra of one target of a model.
"""
declare!(m::Model, name::Symbol, alg::AbstractAlgebra; kind::TargetKind=Parameter, value_type::Type=Float64) =
    (declare!(m.space, Target(name, kind), alg; value_type); m)

"""
    Program(model, atoms...)
    program(model, atoms...)

A program whose declaration table is the model's.
"""
Program(m::Model, atoms::Atom...) = Program(collect(atoms); space=m.space)
Program(m::Model, atoms::AbstractVector{<:Atom}) = Program(collect(atoms); space=m.space)

"""
    program(model, atoms...)

A program whose declaration table is the model's.
"""
program(m::Model, atoms...) = Program(m, atoms...)

"""
    check_targets(program, model)

Every target the program touches must have a selector in the model.
"""
function check_targets(p::Program, m::Model)
    missing_targets = Target[]
    for a in p.atoms, t in atom_targets(a)
        table = is_state(t) ? m.indexing.states : m.indexing.parameters
        haskey(table, t.name) || push!(missing_targets, t)
    end
    isempty(missing_targets) ||
        error("Program targets not present in model: ", join(unique(missing_targets), ", "))
    return p
end

"""
    check_invariants(model, u_before, u_after)

Check each invariant of the model on a state before and after a pulse.
"""
function check_invariants(m::Model, u_before, u_after; atol=1e-8)
    for inv in m.invariants
        if inv isa Conserved
            sel = [m.indexing.states[s] for s in inv.states]
            before = sum(u_before[s] for s in sel)
            after = sum(u_after[s] for s in sel)
            isapprox(before, after; atol=atol * max(1, abs(before))) ||
                throw(InvariantViolation(inv, "sum of $(inv.states) changed from $before to $after"))
        elseif inv isa Nonnegative
            for s in inv.states
                v = u_after[m.indexing.states[s]]
                v >= 0 || throw(InvariantViolation(inv, "state $s became negative ($v)"))
            end
        end
    end
    return nothing
end

# -------------------------------------------------------------- augment ---

"""
    target_map(morphism) -> Dict{Target,Target}

Extension hook: the map of targets induced by a model morphism.
"""
function target_map end

"""
    strata(model_object) -> Dict{Target,Any}

Extension hook: the stratum label of each stratified target.
"""
function strata end

"""
    stratify(base, strata, types, base_types, strata_types)

Extension hook: stratify a base model by a strata model over a type system,
returning the stratified model object and the two projections.
"""
function stratify end

"""
    typed_by(net, types, transition_types)

Extension hook: the typing morphism of a net into a type system.
"""
function typed_by end

"""
    dom(morphism)

Domain of a model morphism.
"""
function dom end

"""
    codom(morphism)

Codomain of a model morphism.
"""
function codom end

"""
    conserves_tokens(net) -> Bool

Extension hook: does every process conserve the total population?
"""
function conserves_tokens end

"""
    augment_flow(model, from, to, rate_name) -> Model

Extension hook: return a model with an added process moving `from` to `to` at
the per-capita rate named `rate_name`, whose baseline value is zero.
"""
function augment_flow end

"""
    extend_parameters(model, p0, additions::Dict{Symbol,<:Real})

Extension hook: return a parameter container like `p0` extended with the given
named entries.
"""
function extend_parameters end

"""
    augment(model, program) -> (model=..., program=..., extend=p0 -> p0′)

Realise every `Flow` atom by adding a process to the model. Each flow becomes
a parameter interval that sets the new rate on the flow's span; the new rate
has baseline zero, so outside the span the augmented model equals the original
(Lean: `augment_restrict`).
"""
function augment(m::Model, p::Program)
    model = m
    atoms = Atom[]
    additions = Dict{Symbol,Float64}()
    for a in p.atoms
        if a.effect isa Flow
            from, to = a.target.name, a.effect.to
            rate_name = Symbol("flow_", from, "_", to, "_", a.id)
            model = augment_flow(model, from, to, rate_name)
            additions[rate_name] = 0.0
            push!(atoms, Atom(a.id, Target(rate_name, Parameter), a.support, SetValue(a.effect.rate), a.metadata))
        else
            push!(atoms, a)
        end
    end
    program = Program(atoms; space=model.space)
    extend = p0 -> isempty(additions) ? p0 : extend_parameters(model, p0, additions)
    return (model=model, program=program, extend=extend)
end
