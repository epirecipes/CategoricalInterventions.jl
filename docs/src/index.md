# CategoricalInterventions.jl

CategoricalInterventions.jl describes, combines, and applies time-varying
interventions in epidemiological models. An intervention is a typed local edit:
scale a rate on a span of time, move people between compartments at an
instant, run a vaccination campaign as a flow. Interventions compose when they
are compatible and are rejected with a precise report when they are not. A
program of interventions applies to any model that exposes its rates and
states, so the same lockdown runs unchanged on an AlgebraicPetri net, a
StockFlow diagram, an AlgebraicDynamics system, or a hand-written ODE.

The algebra behind this is small and is verified: Lean proves the laws of
composition, the narrative (sheaf and cosheaf) structure of programs, the
action of programs on schedules, transport along model morphisms, and the
callback-lowering algorithm. Lean does not verify the ODE solver or Catlab.
The [verified properties](@ref verified) page lists every claim the
documentation makes with the theorem behind it.

## Where to go

- [Quick start](@ref quickstart): a lockdown and a vaccination on an SIR model in
  ten lines.
- [Concepts](@ref concepts): targets, supports, effects, algebras, conflicts,
  epochs, in plain language.
- How-to guides for [AlgebraicPetri](@ref howto-algebraicpetri),
  [StockFlow](@ref howto-stockflow), [AlgebraicDynamics](@ref howto-algebraicdynamics),
  [discrete-time models](@ref howto-discrete), [flows](@ref howto-flows),
  [transport and stratification](@ref howto-transport), [temporal queries](@ref howto-queries),
  and [inferring interventions](@ref howto-infer).
- [Semantics](@ref semantics): exactly what a program means and what the callback
  guarantees.
- [The categorical view](@ref categorical): for readers who want the mathematics,
  with every definition linked to its Lean theorem.
- [Verified properties](@ref verified) and the [API reference](@ref api-reference).

## Module

```@docs
CategoricalInterventions
```

## Installation

The package is not yet registered. From a clone:

```julia
using Pkg
Pkg.develop(path="path/to/CategoricalInterventions.jl")
```

Load the extensions you need by loading their packages: `DiffEqCallbacks`
(with an integrator such as `OrdinaryDiffEq`) for simulation,
`AlgebraicPetri`, `StockFlow`, or `AlgebraicDynamics` for model construction,
and `Plots` for Gantt charts.
