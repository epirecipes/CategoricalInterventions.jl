# [Quick start](@id quickstart)

```@meta
CurrentModule = CategoricalInterventions
```

Build an SIR model, describe two interventions, and simulate.

```julia
using CategoricalInterventions
using AlgebraicPetri, LabelledArrays, OrdinaryDiffEq, DiffEqCallbacks

sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R))
model = Model(sir)            # rates :inf, :rec; states :S, :I, :R

program = @interventions model begin
    lockdown    = scale(:inf, 0.5; during=5..25)
    vaccination = transfer(:S => :R, 50; at=15)
end

u0 = LVector(S=990.0, I=10.0, R=0.0)
p0 = LVector(inf=0.05 * 10 / 1000, rec=0.25)
sol = simulate(model, program; u0, p0, tspan=(0.0, 40.0), alg=Tsit5(), saveat=0.5)
```

Read the program back in words:

```julia
explain(program; baseline=Dict(:inf => p0.inf))
```

```text
Epochs:
  [5, 25)  lockdown
      inf: 0.0005 → 0.00025  (scale(0.5))
Pulses:
  at 15  vaccination: S transfer(50 → R)
```

What happened:

- `Model(sir)` read the net's transitions as rate targets and its species as
  state targets, gave rates the set-then-scale algebra and states the additive
  algebra, and added a conservation invariant because every transition
  conserves tokens.
- `@interventions` turned each line into an atom named by its left-hand side and
  checked the program against the model's declarations.
- `simulate` lowered the program to a solver callback, built the ODE problem
  from the net's vector field, and solved it.

Plot the supports as a Gantt chart with `plot(program)` once `Plots` is
loaded, and inspect the epochs directly:

```jldoctest quick
julia> using CategoricalInterventions

julia> space = TargetSpace(); declare!(space, :inf, Affine(Multiplicative()));

julia> program = @interventions space begin
           lockdown = scale(:inf, 0.5; during=5..25)
           masks    = scale(:inf, 0.8; during=20..40)
       end;

julia> [e.support for e in epochs(program)]
3-element Vector{Span{Int64}}:
 [5, 20)
 [20, 25)
 [25, 40)

julia> apply(program, Dict(:inf => 1.0))[2].values[:inf]
0.4
```

Next: [Concepts](@ref concepts) for the vocabulary, or the how-to guide for your
modelling framework.
