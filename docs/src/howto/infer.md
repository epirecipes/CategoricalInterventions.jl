# [Inferring interventions from schedules](@id howto-infer)

Given a baseline schedule and an observed one on the same grid, recover a
program:

```julia
times = collect(0.0:1.0:50.0)
baseline = Dict(:beta => fill(0.3, 51))
observed = Dict(:beta => fitted_beta)              # piecewise-constant fit
space = TargetSpace(); declare!(space, :beta, Affine(Multiplicative()))
program = infer(baseline, observed, times; space)
apply(program, baseline, times)[:beta] ≈ observed[:beta]   # true
```

One atom is produced per maximal run of constant ratio (multiplicative
algebras) or difference (additive algebras). Absolute assignments in the
observed schedule are recovered as ratios. The last span ends one grid step
after the last grid time.
