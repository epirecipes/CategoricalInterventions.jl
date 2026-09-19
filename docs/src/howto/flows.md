# [Flows and pulses](@id howto-flows)

A **pulse** acts at an instant. `transfer(:S => :R, 50; at=15)` moves 50
people in one atom and conserves the total; `add(:I, 5; at=20)` seeds
infections; `set(:R, 0.0; at=0)` resets a compartment. Pulses are checked
against the model's invariants:

```julia
push!(model.invariants, Nonnegative([:S]))
try
    simulate(model, Program(model, add(:S, -2000.0; at=5)); u0, p0, tspan, alg=Tsit5())
catch e
    e isa InvariantViolation && println(sprint(showerror, e))
end
```

A **flow** acts over a span at a rate: `flow(:S => :R; rate=0.02, during=10..30)`
is a vaccination campaign moving a fraction of `S` per unit time. `simulate`
realises flows by augmentation; you can also do it explicitly:

```julia
campaign = Program(model, flow(:S => :R; rate=0.02, during=10..30, id=:campaign))
aug = augment(model, campaign)
aug.model            # the Petri net with a new transition S → R
aug.program          # set(:flow_S_R_campaign, 0.02) during [10, 30)
aug.extend(p0)       # p0 with the new rate at baseline 0
```

Augmentation is implemented for AlgebraicPetri models; the new rate has
baseline zero, so outside the flow's span the augmented model equals the
original.
