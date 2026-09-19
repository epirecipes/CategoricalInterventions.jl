# [ModelingToolkit models](@id howto-modelingtoolkit)

Load `ModelingToolkit` and `SymbolicIndexingInterface` and build the model
from a completed system:

```julia
using CategoricalInterventions, ModelingToolkit, OrdinaryDiffEq, DiffEqCallbacks, SymbolicIndexingInterface
using ModelingToolkit: t_nounits as t, D_nounits as D

@parameters inf rec
@variables S(t) I(t) R(t)
@named sir = ODESystem([D(S) ~ -inf * S * I, D(I) ~ inf * S * I - rec * I, D(R) ~ rec * I], t)
model = Model(structural_simplify(sir))       # rates :inf, :rec; states :S, :I, :R

program = @interventions model begin
    lockdown    = scale(:inf, 0.5; during=5..25)
    vaccination = transfer(:S => :R, 50; at=15)
end
sol = simulate(model, program; u0=[S => 990.0, I => 10.0, R => 0.0], p0=[inf => 0.0005, rec => 0.25],
               tspan=(0.0, 40.0), alg=Tsit5(), saveat=0.5)
```

Parameters are located by symbolic selectors through
SymbolicIndexingInterface, so the callback reads and writes the integrator's
`MTKParameters` object; unknowns are located by position. Because `u0` and
`p0` are symbolic maps, the callback captures its baseline from the integrator
when the solve starts. ModelingToolkit's own initialisation parameters are not
exposed as targets. Flows are not supported for ModelingToolkit models; add
the process to the system instead. Both `ModelingToolkit` and
`CategoricalInterventions` export `parameters`, so qualify that name when
both are loaded.
