/-!
*Source: `Interval.lean`*

# Half-open intervention intervals

Intervention supports are half-open intervals `[start, stop)`. This file proves
the basic facts used by the Julia implementation:

| # | Result | Status |
|---|--------|--------|
| 1 | The start time is contained in a valid interval | ✅ |
| 2 | The stop time is not contained in a valid interval | ✅ |
| 3 | If `I.stop ≤ J.start`, then `I` and `J` do not overlap | ✅ |
| 4 | Disjoint intervals have no overlap | ✅ |
-/

namespace CategoricalInterventionsProofs

/-- A half-open interval `[start, stop)`. -/
structure Interval where
  start : Nat
  stop : Nat
  valid : start < stop
deriving Repr

/-- Membership in a half-open interval. -/
def Contains (I : Interval) (t : Nat) : Prop :=
  I.start ≤ t ∧ t < I.stop

/-- Two half-open intervals overlap when each begins before the other ends. -/
def Overlaps (I J : Interval) : Prop :=
  I.start < J.stop ∧ J.start < I.stop

/-- Disjointness is the negation of overlap. -/
def Disjoint (I J : Interval) : Prop :=
  ¬ Overlaps I J

theorem start_mem (I : Interval) : Contains I I.start := by
  exact ⟨Nat.le_refl I.start, I.valid⟩

theorem stop_not_mem (I : Interval) : ¬ Contains I I.stop := by
  intro h
  exact (Nat.lt_irrefl I.stop) h.right

theorem disjoint_of_stop_le_start {I J : Interval}
    (h : I.stop ≤ J.start) : Disjoint I J := by
  intro overlap
  exact (Nat.not_lt_of_ge h) overlap.right

theorem no_overlap_of_disjoint {I J : Interval}
    (h : Disjoint I J) : ¬ Overlaps I J :=
  h

end CategoricalInterventionsProofs
