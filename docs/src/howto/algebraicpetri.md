# [AlgebraicPetri models](@id howto-algebraicpetri)

Load `AlgebraicPetri` and build the model from a labelled net:

```julia
using CategoricalInterventions, AlgebraicPetri, LabelledArrays, OrdinaryDiffEq, DiffEqCallbacks
sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R))
model = Model(sir)
```

Transitions become parameter targets with the set-then-scale algebra;
species become state targets with the additive algebra. A `Conserved`
invariant over all species is added when every transition has as many inputs
as outputs. Tuple labels from product nets are flattened with `_`.

Parameters and states are labelled, so use `LVector`s:

```julia
u0 = LVector(S=990.0, I=10.0, R=0.0)
p0 = LVector(inf=0.0005, rec=0.25)
program = @interventions model begin
    lockdown = scale(:inf, 0.5; during=5..25)
end
sol = simulate(model, program; u0, p0, tspan=(0.0, 40.0), alg=Tsit5(), saveat=0.5)
```

To change an algebra, redeclare the target on the model:

```julia
declare!(model, :inf, LatestWins())
```

Morphisms of nets transport programs: see [transport](@ref howto-transport).
Flows add transitions to the net: see [flows](@ref howto-flows).
