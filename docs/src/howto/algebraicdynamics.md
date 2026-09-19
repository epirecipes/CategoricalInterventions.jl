# [AlgebraicDynamics models](@id howto-algebraicdynamics)

AlgebraicDynamics composes resource sharers into a system with a positional
state vector, so name the states in order and label the parameters with a
`ComponentArray`:

```julia
using CategoricalInterventions, AlgebraicDynamics, Catlab, ComponentArrays, OrdinaryDiffEq, DiffEqCallbacks
using Catlab.Programs
using Catlab.WiringDiagrams: oapply

infection = ContinuousResourceSharer{Float64}(2, (u, p, t) -> (r = p.inf * u[1] * u[2]; [-r, r]))
recovery  = ContinuousResourceSharer{Float64}(2, (u, p, t) -> (r = p.rec * u[1]; [-r, r]))
pattern = @relation (S, I, R) begin
    infection(S, I)
    recovery(I, R)
end
sys = oapply(pattern, [infection, recovery])

model = Model(sys; states=[:S, :I, :R], parameters=[:inf, :rec])
u0 = [990.0, 10.0, 0.0]
p0 = ComponentArray(inf=0.0005, rec=0.25)
```

A `DiscreteResourceSharer` gives a model with `kind=:discrete`; see
[discrete-time models](@ref howto-discrete).
