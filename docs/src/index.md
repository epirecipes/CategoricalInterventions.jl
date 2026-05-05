# CategoricalInterventions.jl

`CategoricalInterventions.jl` is an experimental Julia package for describing,
combining, and applying time-varying interventions in epidemiological models.
It represents interventions as typed local edits over half-open time intervals,
with explicit rules for composing overlapping edits on the same model target.

The package is built around three ideas:

- **typed targets** identify what an intervention changes, such as a model
  parameter, state variable, process, or observation;
- **interval support** records when the edit is active;
- **combination algebras** make overlap behavior explicit, so conflicting
  interventions fail early while compatible interventions can compose.

## What the docs cover

Use the pages in this manual in order if you are new to the package:

1. [Tutorial](@ref tutorial) introduces targets, intervals, composition, epoch
   refinement, and discrete schedules.
2. [Callback lowering](@ref callback-lowering) explains how intervention programs become
   `DiffEqCallbacks.jl` callbacks for SciML integrators, including
   AlgebraicPetri-style state and parameter containers.
3. [Categorical structures](@ref categorical-structures) documents the Catlab representations used for
   epoch maps and intervention-program ACSets.
4. [Unicode syntax](@ref unicode-syntax) lists the ContACT.jl-style shorthand operators.
5. [API reference](@ref api-reference) includes all exported public symbols.

Rendered Quarto vignettes in the repository complement these docs with
end-to-end examples using AlgebraicPetri.jl, StockFlow.jl, and
AlgebraicDynamics.jl.

## Installation for local development

From the package directory:

```julia
using Pkg
Pkg.activate(".")
Pkg.instantiate()
```

Load the package with:

```julia
using CategoricalInterventions
```

Load `DiffEqCallbacks` as well when using callback lowering:

```julia
using DiffEqCallbacks
```

## Public API completeness

The documentation build uses Documenter with `checkdocs = :exports`, so exported
symbols are checked against the manual. The [API reference](@ref api-reference)
is the public surface for the package.
