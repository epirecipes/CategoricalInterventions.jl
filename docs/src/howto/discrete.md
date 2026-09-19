# [Discrete-time models](@id howto-discrete)

A model built with `kind=:discrete` is solved as a `DiscreteProblem`. Pass the
map's time step through `simulate`:

```julia
using CategoricalInterventions, OrdinaryDiffEq, DiffEqCallbacks
rate_to_proportion(r, δt) = 1 - exp(-r * δt)
function sir_map!(du, u, p, t)
    S, I, R = u
    infection = rate_to_proportion(p[1] * I / 1000, 0.1) * S
    recovery = rate_to_proportion(p[2], 0.1) * I
    du .= (S - infection, I + infection - recovery, R + recovery)
    nothing
end
model = Model(sir_map!; parameters=Dict(:inf => 1, :rec => 2), states=Dict(:S => 1, :I => 2, :R => 3), kind=:discrete)
program = @interventions model begin
    lockdown = scale(:inf, 0.5; during=5.0..25.0)
end
sol = simulate(model, program; u0=[990.0, 10.0, 0.0], p0=[0.5, 0.25], tspan=(0.0, 40.0), alg=FunctionMap(), dt=0.1)
```

The same program applies to the continuous and the discrete model. Pulses at
step `t` are applied before the update at `t`. To work with schedules on a
grid directly, `sample(program, grid)` pulls the program back to grid indices,
and `apply(program, schedules, times)` evaluates it pointwise; the two agree
(`apply_discrete_eq`).
