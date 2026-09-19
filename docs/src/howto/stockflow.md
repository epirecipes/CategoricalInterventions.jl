# [StockFlow models](@id howto-stockflow)

StockFlow.jl currently supports Julia 1.9 to 1.11, so use a 1.11 environment.

```julia
using CategoricalInterventions, StockFlow, StockFlow.Syntax, LabelledArrays, OrdinaryDiffEq, DiffEqCallbacks
sir = @stock_and_flow begin
    :stocks
    S; I; R
    :parameters
    inf; rec
    :dynamic_variables
    v_infection = inf * S * I
    v_recovery = rec * I
    :flows
    S => f_infection(v_infection) => I
    I => f_recovery(v_recovery) => R
    :sums
    N = [S, I, R]
end
model = Model(sir)
```

Parameters become rate targets and stocks become state targets. Targets are
located by label, so `u0` and `p0` must be `LVector`s (a plain `Vector` gives
a clear error); the rest is as for AlgebraicPetri. `augment` is
not available for StockFlow models in this version, so flows must be written
into the diagram directly.
