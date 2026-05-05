# CategoricalInterventions.jl

`CategoricalInterventions.jl` is an experimental Julia package for composing
time-varying interventions in epidemiological models. It implements the framework
sketched in `../category_theory_interventions.md`: interventions are local, typed
edits to a model narrative over a poset of time intervals.

The package uses [Catlab.jl](https://algebraicjulia.github.io/Catlab.jl/) for base
categorical structures:

- `FinFunction` maps sampled time points to normalized intervention epochs.
- an ACSet schema records intervention atoms, targets, supports, and effects.

## Core concepts

An intervention atom has:

- a target, such as `:beta` or `:I`;
- a half-open support interval `[start, stop)`;
- an effect, such as `SetValue`, `Add`, or `Scale`;
- an optional combination algebra for overlapping same-target interventions.

Different targets can overlap freely. Same-target interventions compose only when
their intervals are disjoint or the target declares an algebra such as
`MultiplicativeAlgebra()`.

## Unicode syntax

The package provides ContACT.jl-style Unicode aliases for common constructors and
operations:

| Symbol | LaTeX tab-completion | Meaning |
| --- | --- | --- |
| `ℙ(:beta)` | `\bbP<TAB>` | parameter target |
| `𝕊(:I)` | `\bbS<TAB>` | state target |
| `𝕀(10, 30)` | `\bbI<TAB>` | half-open interval `[10, 30)` |
| `ι(:id, target, interval, effect)` | `\iota<TAB>` | intervention atom |
| `Π(atom1, atom2)` | `\Pi<TAB>` | intervention program |
| `≜(x)`, `δ(x)`, `κ(x)` | `\triangleq<TAB>`, `\delta<TAB>`, `\kappa<TAB>` | set, add, scale effects |
| `p ⊕ q` | `\oplus<TAB>` | compose programs/atoms |
| `p ⊙ baseline` | `\odot<TAB>` | apply a program |
| `t ∈ interval`, `a ∩ b` | `\in<TAB>`, `\cap<TAB>` | containment and interval intersection |

For example:

```julia
β = ℙ(:beta; value_type = Float64, algebra = MultiplicativeAlgebra())
closure = ι(:closure, β, 𝕀(10, 30), κ(0.6))
program = Π(closure)
program ⊙ Dict(:beta => 0.30)
```

## Example

```julia
using CategoricalInterventions

beta = Target(:beta; kind=Parameter, value_type=Float64)
gamma = Target(:gamma; kind=Parameter, value_type=Float64)

school_closure = InterventionAtom(
    :school_closure,
    beta,
    Interval(10, 30),
    Scale(0.6),
)

case_isolation = InterventionAtom(
    :case_isolation,
    gamma,
    Interval(20, 40),
    SetValue(0.25),
)

program = compose_interventions(
    InterventionProgram(school_closure),
    InterventionProgram(case_isolation),
)

epochs = epochize(program)
```

The epoch refinement is:

```text
[10, 20): beta scaled by 0.6
[20, 30): beta scaled by 0.6 and gamma set to 0.25
[30, 40): gamma set to 0.25
```

Apply to a baseline:

```julia
apply_interventions(program, Dict(:beta => 0.30, :gamma => 0.10))
```

## Same-target conflicts

By default, overlapping interventions on the same target are rejected:

```julia
a = InterventionAtom(:closure, beta, Interval(10, 30), Scale(0.6))
b = InterventionAtom(:mandate, beta, Interval(20, 40), Scale(0.8))

compose_interventions(InterventionProgram(a), InterventionProgram(b)) # throws
```

To allow multiplicative overlap:

```julia
beta_mult = Target(
    :beta;
    kind=Parameter,
    value_type=Float64,
    algebra=MultiplicativeAlgebra(),
)
```

Now overlapping `Scale` effects combine by multiplication.

## Discrete schedules

```julia
times = collect(0:5)
baseline = Dict(:beta => fill(0.30, length(times)))
program = InterventionProgram(
    InterventionAtom(:closure, beta_mult, Interval(2, 5), Scale(0.5)),
)

apply_discrete(program, baseline, times)
```

## Catlab representations

```julia
epochs = epochize(program)
f = epoch_finfunction(times[3:5], epochs)
acset = as_acset(program)
```

The `FinFunction` records a map from sampled times to epochs; the ACSet records the
intervention program as categorical data.

## Formal proofs (Lean 4)

The `proofs/` directory contains a small Lean 4 formalization of intervention
program laws:

| Property | File |
| --- | --- |
| Half-open interval membership at start/stop | `Interval.lean` |
| Disjoint intervals cannot overlap | `Interval.lean` |
| Raw intervention program composition is associative | `Composition.lean` |
| Empty program is a left/right identity | `Composition.lean` |
| Disjoint same-target atoms are conflict-free | `Compatibility.lean` |

Build proofs with:

```bash
cd proofs && lake build
```

## Vignettes

The `vignettes/` directory contains Quarto `.qmd` files, each in its own numbered
directory. They progress from simple intervention atoms and epochization through
composition rules, discrete schedules, Catlab representations, and SIR models
implemented with AlgebraicPetri.jl, StockFlow.jl, and AlgebraicDynamics.jl. The
AlgebraicDynamics examples include both continuous-time ODEs and discrete-time
difference equations solved with `FunctionMap`. The SIR vignettes use shared
parameterizations and include direct-equation or direct-map cross-checks so the
representations give matching trajectories. The later vignettes include Plots.jl
figures, with Markdown figure assets stored beside the rendered outputs.

Render a vignette from its directory with the vignette environment, for example:

```bash
cd vignettes/04-algebraicpetri-sir
JULIA_PROJECT=.. quarto render algebraicpetri-sir.qmd
```

The StockFlow and AlgebraicDynamics-specific vignettes have local `Project.toml`
files to isolate their dependency constraints. They are pinned in their Quarto
frontmatter to Julia 1.11 via `julia.exeflags`.

## Lowering to DiffEqCallbacks for AlgebraicPetri models

AlgebraicPetri ODE models lower to standard SciML problems whose integrators store
species/state values in `integrator.u` and transition rates/parameters in
`integrator.p`. `CategoricalInterventions.jl` can lower an intervention program to a
`DiffEqCallbacks.PresetTimeCallback` by giving target labels for `LabelledArrays`
states and parameters:

```julia
using AlgebraicPetri
using OrdinaryDiffEq
using DiffEqCallbacks
using CategoricalInterventions

# Suppose an AlgebraicPetri model has species [:S, :I, :R]
# and rates/parameters [:beta, :gamma].
indexing = PetriIndexing(
    parameters = [:beta, :gamma],
    states = [:S, :I, :R],
)

beta = Target(
    :beta;
    kind = Parameter,
    value_type = Float64,
    algebra = MultiplicativeAlgebra(),
)
susceptible = Target(:S; kind = State, value_type = Float64, algebra = AdditiveAlgebra())
recovered = Target(:R; kind = State, value_type = Float64, algebra = AdditiveAlgebra())

program = InterventionProgram(
    InterventionAtom(:school_closure, beta, Interval(10.0, 30.0), Scale(0.6)),
    InterventionAtom(:vaccinate_from_s, susceptible, Interval(20.0, 21.0), Add(-50.0)),
    InterventionAtom(:vaccinate_to_r, recovered, Interval(20.0, 21.0), Add(50.0)),
)

cb = to_callback(program, indexing; baseline_p = p0)

# prob may be an ODEProblem generated from AlgebraicPetri:
# prob = ODEProblem(vectorfield(petri_model), u0, (0.0, 60.0), p)
# sol = solve(prob, Tsit5(); callback = cb)
```

Parameter-like interventions (`Parameter`, `Process`, and `Observation`) are applied
as interval effects: the callback resets only the selectors targeted by the program
to their baseline values and then applies the effects active at the current event
time. Intervals already active at the solve start are applied during callback
initialization. State interventions are pulses at `support.start` and mutate
`integrator.u` directly. State transfers can be represented by paired pulses on
different state labels, such as `Add(-50.0)` to `:S` and `Add(50.0)` to `:R` for
vaccination. For unlabeled plain vectors, pass explicit selector maps such as
`PetriIndexing(parameters = Dict(:beta => 1), states = Dict(:I => 2))`; labelled
and positional selectors can be mixed between parameters and states.

## Status

This is a research prototype intended to support experimentation with categorical
intervention composition. It is not registered.
