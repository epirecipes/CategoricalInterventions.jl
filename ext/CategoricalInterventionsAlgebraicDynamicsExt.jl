module CategoricalInterventionsAlgebraicDynamicsExt

using AlgebraicDynamics
using AlgebraicDynamics.UWDDynam: ContinuousResourceSharer, DiscreteResourceSharer, nstates
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

end # module
