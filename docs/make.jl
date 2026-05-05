using Pkg

pkg_root = dirname(@__DIR__)
Pkg.develop(PackageSpec(path=pkg_root))
Pkg.instantiate()

using CategoricalInterventions
using DiffEqCallbacks
using Documenter

makedocs(;
    modules=[CategoricalInterventions],
    sitename="CategoricalInterventions.jl",
    authors="Simon Frost and contributors",
    doctest=false,
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
        "Tutorial" => "tutorial.md",
        "Callback lowering" => "callbacks.md",
        "Categorical structures" => "categorical.md",
        "Unicode syntax" => "unicode.md",
        "API reference" => "api.md",
    ],
)
