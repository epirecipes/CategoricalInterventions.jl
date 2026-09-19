using Pkg

pkg_root = dirname(@__DIR__)
Pkg.develop(PackageSpec(path=pkg_root))
Pkg.instantiate()

include(joinpath(@__DIR__, "ledger.jl"))
generate_ledger(pkg_root)

using CategoricalInterventions
using DiffEqCallbacks
using Documenter

makedocs(;
    modules=[CategoricalInterventions],
    sitename="CategoricalInterventions.jl",
    authors="Simon Frost and contributors",
    doctest=true,
    checkdocs=:exports,
    warnonly=false,
    remotes=nothing,
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        edit_link=nothing,
        repolink=nothing,
    ),
    pages=[
        "Home" => "index.md",
        "Quick start" => "quickstart.md",
        "Concepts" => "concepts.md",
        "How-to" => [
            "AlgebraicPetri" => "howto/algebraicpetri.md",
            "StockFlow" => "howto/stockflow.md",
            "AlgebraicDynamics" => "howto/algebraicdynamics.md",
            "Discrete time" => "howto/discrete.md",
            "Flows and pulses" => "howto/flows.md",
            "Transport and stratification" => "howto/transport.md",
            "Temporal queries" => "howto/queries.md",
            "Inferring interventions" => "howto/infer.md",
        ],
        "Semantics" => "semantics.md",
        "The categorical view" => "categorical.md",
        "Verified properties" => "verified.md",
        "Unicode syntax" => "unicode.md",
        "API reference" => "api.md",
    ],
)
