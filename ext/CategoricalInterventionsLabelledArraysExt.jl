module CategoricalInterventionsLabelledArraysExt

using LabelledArrays
using CategoricalInterventions
const CI = CategoricalInterventions

function CI.extend_parameters(::Model, p0::LArray, additions::AbstractVector{<:Pair})
    names = collect(propertynames(p0))
    vals = Any[p0[n] for n in names]
    for (k, v) in additions
        push!(names, k); push!(vals, v)
    end
    return LVector(; (names .=> vals)...)
end

end # module
