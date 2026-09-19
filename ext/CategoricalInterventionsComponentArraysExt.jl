module CategoricalInterventionsComponentArraysExt

using ComponentArrays
using CategoricalInterventions
const CI = CategoricalInterventions

function CI.extend_parameters(::Model, p0::ComponentArray, additions::AbstractVector{<:Pair})
    names = collect(keys(p0))
    pairs = Any[n => p0[n] for n in names]
    append!(pairs, [k => v for (k, v) in additions])
    return ComponentArray(; pairs...)
end

end # module
