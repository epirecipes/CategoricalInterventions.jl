module CategoricalInterventionsModelingToolkitExt

using ModelingToolkit
using SymbolicIndexingInterface: getp, setp, variable_index, parameter_symbols, variable_symbols
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    MTKSelector(symbol, getter, setter)

A symbolic parameter selector: reads and writes an `MTKParameters` object
through SymbolicIndexingInterface.
"""
struct MTKSelector
    sym::Any
    get::Any
    set::Any
end
Base.show(io::IO, s::MTKSelector) = print(io, "MTKSelector(", s.sym, ")")
CI._getp(p, sel::MTKSelector) = sel.get(p)
CI._setp!(p, sel::MTKSelector, v) = (sel.set(p, v); p)

_name(x) = Symbol(first(split(string(x), "(")))   # S(t) -> :S, inf -> :inf

# ModelingToolkit 9/10 build `ODESystem`s; 11 builds `System`s.
const _SystemType = Union{[getproperty(ModelingToolkit, n) for n in (:System, :ODESystem, :AbstractSystem) if isdefined(ModelingToolkit, n)]...}

"""
    Model(sys::ODESystem; kind=:continuous, invariants=[], rate_algebra=Affine(Multiplicative()), state_algebra=Additive())

A model from a completed ModelingToolkit system. Parameters become rate
targets located by symbolic selectors; unknowns become state targets located
by position. `u0` and `p0` passed to `simulate` are ModelingToolkit maps; the
callback baseline is captured from the integrator. Flows are not supported
for ModelingToolkit models.
"""
function CI.Model(sys::_SystemType; kind::Symbol=:continuous, invariants=CI.AbstractInvariant[],
                  rate_algebra=Affine(Multiplicative()), state_algebra=Additive(), value_type::Type=Float64)
    ModelingToolkit.iscomplete(sys) || error("pass a completed system: complete(sys) or structural_simplify(sys)")
    psyms = [p for p in parameter_symbols(sys) if !startswith(string(p), "Initial(")]   # skip MTK's initialisation parameters
    xsyms = sort(collect(variable_symbols(sys)); by=x -> variable_index(sys, x))
    params = Dict{Symbol,Any}(_name(p) => MTKSelector(p, getp(sys, p), setp(sys, p)) for p in psyms)
    states = Dict{Symbol,Any}(_name(x) => variable_index(sys, x) for x in xsyms)
    pnames = unique(Symbol[_name(p) for p in psyms])
    snames = Symbol[_name(x) for x in xsyms]
    indexing = Indexing(params, states, pnames, snames)
    space = TargetSpace()
    for n in pnames
        declare!(space, Target(n, Parameter), rate_algebra; value_type)
    end
    for n in snames
        declare!(space, Target(n, State), state_algebra; value_type)
    end
    return Model(sys, space, indexing, collect(CI.AbstractInvariant, invariants), kind,
                 Dict{Symbol,Any}(:source => :ModelingToolkit, :baseline_from_integrator => true))
end

CI._augment_flow(::Val{:ModelingToolkit}, m::Model, from::Symbol, to::Symbol, rate_name::Symbol) =
    error("Flows are not supported for ModelingToolkit models; add the process to the system instead")

end # module
