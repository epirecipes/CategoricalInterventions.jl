# Changelog

## v0.2.0 (2026-09-19)

A redesign around a verified algebraic core. See `design/REVIEW.md` for the
assessment of v0.1 and `design/PLAN.md` for the framework and the
implementation notes.

### Added
- Partial commutative monoids as combination algebras: `Reject`,
  `Multiplicative`, `Additive`, `Cap`, `Floor`, `Affine` (set-then-scale);
  ordered policies `LatestWins`, `HighestPriority` as a separate class.
- `TargetSpace` and `Model`: algebras and value types declared once per
  target; models built from AlgebraicPetri nets, StockFlow diagrams,
  AlgebraicDynamics systems, or plain functions; `Conserved` and
  `Nonnegative` invariants.
- `Instant` supports for pulses; `Transfer` (one-atom conserving move) and
  `Flow` (realised by `augment`).
- Plain constructors `scale`, `set`, `add`, `cap`, `floor_at`, `custom`,
  `transfer`, `flow`, and the `@interventions` block; `explain`, `table`,
  `plot`.
- `persistent` and `cumulative` narratives; `restrict`; `sample`; `lower`
  and `hold_last`; `simulate`.
- `pushforward` and `lift` along target maps and Petri-net morphisms;
  `stratify` for AlgebraicPetri models.
- Catlab-backed `NarrativeWindow` with `truth_value`, `describe`, and the
  Heyting operations.
- `infer`: recover a program from a baseline and an observed schedule.
- Lean 4 + Mathlib proofs (148 theorems) and a generated claims ledger in
  the documentation; property tests mirroring the theorems.
- Extensions for LabelledArrays, ComponentArrays, Plots.

### Changed
- Conflict reports name both atoms, the overlap, and a resolving algebra.
- `epochs(check=false)` records conflicts instead of throwing.
- The callback captures its baseline per solve and releases it afterwards.
- v0.1 names remain as aliases: `InterventionAtom`, `InterventionProgram`,
  `compose_interventions`, `epochize`, `apply_interventions`,
  `apply_discrete`, `PetriIndexing`, `callback_times`.

### Removed
- `epoch_finfunction`, `as_acset`, and `InterventionProgramData` (replaced by
  the narrative window).
- Algebra and value type keywords on `Target` (now on the model or space).
