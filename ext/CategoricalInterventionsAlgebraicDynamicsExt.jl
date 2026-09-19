module CategoricalInterventionsAlgebraicDynamicsExt

using AlgebraicDynamics
using AlgebraicDynamics.UWDDynam: ContinuousResourceSharer, DiscreteResourceSharer, nstates, eval_dynamics
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    Model(sys::ContinuousResourceSharer; states, parameters, kwargs...)
    Model(sys::DiscreteResourceSharer; states, parameters, kwargs...)

AlgebraicDynamics systems keep a positional state vector, so `states` gives the
names in order; `parameters` names the labelled parameter container.
"""
function CI.Model(sys::ContinuousResourceSharer; states::AbstractVector{Symbol}, parameters, invariants=CI.AbstractInvariant[], kw...)
    length(states) == nstates(sys) || error("expected $(nstates(sys)) state names")
    invoke(CI.Model, Tuple{Any}, sys; parameters, states=Dict(s => i for (i, s) in enumerate(states)), kind=:continuous,
           invariants, kw..., metadata=Dict{Symbol,Any}(:source => :AlgebraicDynamics))
end
function CI.Model(sys::DiscreteResourceSharer; states::AbstractVector{Symbol}, parameters, invariants=CI.AbstractInvariant[], kw...)
    length(states) == nstates(sys) || error("expected $(nstates(sys)) state names")
    invoke(CI.Model, Tuple{Any}, sys; parameters, states=Dict(s => i for (i, s) in enumerate(states)), kind=:discrete,
           invariants, kw..., metadata=Dict{Symbol,Any}(:source => :AlgebraicDynamics))
end

"""
Flows on an AlgebraicDynamics model: convert the system to a plain function of
`(u, p, t)` and use the generic wrapper.
"""
function CI._augment_flow(::Val{:AlgebraicDynamics}, m::Model, from::Symbol, to::Symbol, rate_name::Symbol)
    sys = m.dynamics
    f = (u, p, t) -> eval_dynamics(sys, u, p, t)
    plain = Model(f, m.space, m.indexing, m.invariants, m.kind, merge(m.metadata, Dict{Symbol,Any}(:source => :function)))
    return CI._augment_flow(Val(:function), plain, from, to, rate_name)
end

end # module
