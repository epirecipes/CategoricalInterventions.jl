# [Semantics](@id semantics)

```@meta
CurrentModule = CategoricalInterventions
```

This page states precisely what a program means. No category theory is
needed; the [categorical view](@ref categorical) gives the same facts their
structural names.

## A program acts on a schedule

A schedule assigns a value to every parameter-like target at every time. A
conflict-free program acts pointwise: at time `t`, take the atoms whose
supports contain `t`, combine their effects on each target with the target's
algebra, and apply the combined effect to the baseline value. So:

- outside every support, the schedule is unchanged (`apply_local`);
- the empty program does nothing (`apply_nil`);
- the order of atoms in a program never changes the result under a partial
  commutative monoid (`apply_comm`);
- applying `P` then `Q` equals applying `P ⊕ Q`, for algebras whose effects
  are actions (`apply_append`); under `Affine`, absolute assignments are
  applied before relative effects regardless of program order, so this holds
  when `Q` is purely relative (`apply_append_affine`);
- restricting the schedule to a sub-window, or resampling it on a grid,
  commutes with applying the program (`apply_pullback`, `apply_discrete_eq`).

[`apply`](@ref) on a scalar baseline returns one value per epoch; on
time-indexed vectors it returns the pointwise result. [`sample`](@ref) pulls a
program back to grid indices, and applying the sampled program at indices
agrees with applying the original at grid values.

## Pulses and flows

A state pulse acts at its instant: the state is rewritten
(`SetValue`, `Add`, or `Transfer`) and the model's invariants are checked. A
`Transfer` removes from one state and adds to another in a single atom, so
conservation holds by construction (`transfer_preserves_sum`).

A flow is not applied directly. [`augment`](@ref) adds a process to the model
with a new rate whose baseline is zero, and turns the flow into a parameter
interval that sets that rate on the flow's span. On the original targets the
augmented program agrees with the original (`augment_restrict`). The modelling
assumption, not proved, is that a process with rate zero does not change the
vector field.

## What the callback guarantees

[`to_callback`](@ref) fires at every span endpoint and every instant. At each
event it resets the program's parameter targets to the baseline, applies the
effects active at that time, then applies the pulses scheduled at that time.
Untargeted parameters are never touched, so independent callbacks compose.
Holding each parameter value from one event to the next reproduces the
program's schedule exactly (`lower_eq_apply`). The baseline is `baseline_p` if
given; otherwise it is captured when the solve starts and released when it
ends, so one callback can be reused across solves with different parameters.

For discrete-time models (`kind=:discrete`), pulses at step `t` are applied
before the update at step `t`.

Lean verifies the algorithm above on a pure model of the integrator. It does
not verify the ODE solver, floating point, or Catlab.
