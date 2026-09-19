# CategoricalInterventions.jl

Composable, time-varying interventions for epidemiological models, with the
algebra behind them verified in Lean.

An intervention is a typed local edit to a model: scale a rate on a span of
time, move people between compartments at an instant, run a vaccination
campaign as a flow. Interventions compose when they are compatible and are
rejected with a precise report when they are not. One program applies unchanged
to any model that exposes its rates and states: an AlgebraicPetri net, a
StockFlow diagram, an AlgebraicDynamics system, a ModelingToolkit system, a
hand-written ODE, or a discrete-time map.

```julia
using CategoricalInterventions
using AlgebraicPetri, LabelledArrays, OrdinaryDiffEq, DiffEqCallbacks

sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R))
model = Model(sir)                       # rates :inf, :rec (set-then-scale); states :S, :I, :R (additive)

program = @interventions model begin
    lockdown    = scale(:inf, 0.5; during=5..25)
    vaccination = transfer(:S => :R, 50; at=15)
    campaign    = flow(:S => :R; rate=0.01, during=30..40)
end

explain(program)
sol = simulate(model, program; u0=LVector(S=990.0, I=10.0, R=0.0),
               p0=LVector(inf=0.0005, rec=0.25), tspan=(0.0, 40.0), alg=Tsit5(), saveat=0.5)
```

## What you get

- **Composition with conflict detection.** Different targets never conflict;
  the same target on disjoint supports never conflicts; overlapping edits on one
  target combine only under the target's declared algebra, and otherwise
  produce a report naming both atoms, the overlap, and an algebra that would
  resolve it. Algebras are partial commutative monoids (`Reject`,
  `Multiplicative`, `Additive`, `Cap`, `Floor`, and `Affine`, "set once, then
  scale"); order-dependent policies (`LatestWins`, `HighestPriority`) are a
  separate class.
- **Epochs and narratives.** A program normalises to epochs on which the active
  set is constant, and reads as a persistent narrative (atoms in force
  throughout a window) and a cumulative narrative (atoms in force at some time
  in it), which satisfy the sheaf and cosheaf gluing equations.
- **One program, many models.** Application to a schedule commutes with
  restriction and resampling, so the same program is correct on continuous and
  grid models, and lowers to a `DiffEqCallbacks` callback whose held values
  equal the schedule exactly.
- **Transport.** Push a program forward along a map of targets, or lift it
  along the projection of a stratified model: define a lockdown once on SIR,
  stratify by age with `stratify`, and `lift` it in one call.
- **Pulses, flows, invariants.** `transfer` conserves population by
  construction; flows are realised by augmenting the model with a new process
  (a transition for Petri nets, a wrapped vector field otherwise);
  `Conserved` and `Nonnegative` invariants are checked at every pulse.
- **Temporal queries.** On a grid window, a program is a subobject of a Catlab
  graph; `describe` reports the five local truth values of Niu et al.'s
  subobject classifier, and `⟹`, `∧`, `¬` are available.
- **Inference.** `infer` recovers a program from a baseline and an observed
  piecewise schedule.

## What is verified

`proofs/` is a Lean 4 development on Mathlib (148 theorems, no `sorry`)
covering supports, effect algebras, conflict-freeness, epochs, narratives,
the action of programs on schedules, transport, the lowering algorithm,
augmentation, and inference. The documentation's
[verified properties](docs/src/verified.md) page lists every claim the manual
makes with the theorem behind it, and the docs build fails if a theorem
disappears. Lean verifies the algebra of programs, their action on schedules,
and the lowering algorithm; it does not verify the ODE solver or Catlab.
`test/laws.jl` exercises the same laws on random programs.

## Layout

| Directory | Contents |
|---|---|
| `src/` | the package: supports, algebras, programs, narratives, semantics, models, lowering, transport, DSL, queries, inference |
| `ext/` | extensions for DiffEqCallbacks, AlgebraicPetri, StockFlow, AlgebraicDynamics, ModelingToolkit, LabelledArrays, ComponentArrays, Plots |
| `proofs/` | Lean 4 + Mathlib proofs; `make build` |
| `docs/` | Documenter manual; `julia --project=docs docs/make.jl` |
| `vignettes/` | Quarto vignettes, one structural idea each |
| `design/` | the v0.1 review and the v0.2 plan |
| `test/` | tests, including property tests mirroring the Lean theorems |

## Building

```julia
using Pkg; Pkg.activate("."); Pkg.instantiate(); Pkg.test()
```

```bash
cd proofs && make build          # Lean 4.30.0, Mathlib v4.30.0 (downloads the cache once)
julia --project=docs docs/make.jl
cd vignettes/01-getting-started && JULIA_PROJECT=.. quarto render getting-started.qmd
```

The package requires Julia 1.11 or later: Catlab 0.17's pullbacks, used by
`stratify`, fail on Julia 1.10. StockFlow.jl supports Julia 1.11 only, so the
vignette that uses it pins that version.

## Status

Research prototype, not registered. The v0.1 names (`InterventionAtom`,
`InterventionProgram`, `compose_interventions`, `epochize`,
`apply_interventions`, `apply_discrete`, `PetriIndexing`, `callback_times`)
remain as aliases.

## Related work

The design note is `../papers/category_theory_interventions.md`. The narrative
structure follows Bumpus, Fairbanks, Karvonen, Leal and Simard, *Towards a
unified theory of time-varying data* (arXiv:2402.00206), and the temporal
logic follows Niu, Osgood, Zelko and Srinivasan, *Temporal sheaf theory for
reconciling temporal complexity within public health modeling* (ACT 2026
submission).
