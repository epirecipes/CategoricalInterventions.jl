module CategoricalInterventionsStockFlowExt

using StockFlow
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    Model(sf::AbstractStockAndFlowF; kind=:continuous, invariants=nothing)

A model whose rates are the diagram's parameters (set-then-scale algebra) and
whose states are its stocks (additive algebra).
"""
function CI.Model(sf::StockFlow.AbstractStockAndFlowF; kind::Symbol=:continuous, invariants=nothing,
                  rate_algebra=Affine(Multiplicative()), state_algebra=Additive(), value_type::Type=Float64)
    stocks = collect(snames(sf))
    params = collect(pnames(sf))
    inv = invariants === nothing ? CI.AbstractInvariant[] : invariants
    return Model(vectorfield(sf); parameters=params, states=stocks, kind, invariants=inv, rate_algebra,
                 state_algebra, value_type, metadata=Dict{Symbol,Any}(:stockflow => sf, :source => :StockFlow))
end

end # module
