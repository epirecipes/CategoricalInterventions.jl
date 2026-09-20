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
        prettyurls=true,
        canonical="https://epirecipes.github.io/CategoricalInterventions.jl/",
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
            "ModelingToolkit" => "howto/modelingtoolkit.md",
            "Discrete time" => "howto/discrete.md",
            "Flows and pulses" => "howto/flows.md",
            "Transport and stratification" => "howto/transport.md",
            "Temporal queries" => "howto/queries.md",
            "Inferring interventions" => "howto/infer.md",
        ],
        "Semantics" => "semantics.md",
        "The categorical view" => "categorical.md",
        "Verified properties" => "verified.md",
        "Vignettes" => "tutorials.md",
        "Unicode syntax" => "unicode.md",
        "API reference" => "api.md",
    ],
)

# Publish the pre-rendered, self-contained vignette pages alongside the manual.
let out = joinpath(@__DIR__, "build", "vignettes")
    mkpath(out)
    for (root, _, files) in walkdir(joinpath(pkg_root, "vignettes")), f in files
        endswith(f, ".html") && cp(joinpath(root, f), joinpath(out, f); force=true)
    end
end

deploydocs(;
    repo="github.com/epirecipes/CategoricalInterventions.jl.git",
    devbranch="main",
    versions=nothing,
    push_preview=false,
)
