using Test
using CategoricalInterventions
using DiffEqCallbacks, SciMLBase
using AlgebraicPetri
using LabelledArrays
using OrdinaryDiffEq
using Random

const CI = CategoricalInterventions

mutable struct FakeIntegrator
    u::Vector{Float64}
    p::Vector{Float64}
    t::Float64
end

function sir_space()
    sp = TargetSpace()
    declare!(sp, :beta, Affine(Multiplicative()); value_type=Float64)
    declare!(sp, :gamma, Affine(Multiplicative()); value_type=Float64)
    declare!(sp, :S, Additive(); kind=State, value_type=Float64)
    declare!(sp, :I, Additive(); kind=State, value_type=Float64)
    declare!(sp, :R, Additive(); kind=State, value_type=Float64)
    return sp
end

@testset "CategoricalInterventions.jl" begin
    include("core.jl")
    include("laws.jl")
    include("models.jl")
    include("queries.jl")
    include("compat.jl")
end
