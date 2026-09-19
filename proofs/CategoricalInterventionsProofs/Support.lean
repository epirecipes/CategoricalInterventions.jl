import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.Linarith

/-!
# Supports: spans and instants on a linear timeline

An intervention is in force on a *support*: either a half-open span `[lo, hi)`
with `lo < hi`, or a single instant `{t₀}` (a pulse).  The timeline `τ` is any
linear order (ℝ, ℤ, or a finite grid).  Every support is order-convex; this is
the only property of supports that the narrative (sheaf/cosheaf) theory needs.

This file generalises the v0.1 `Interval.lean` (which was `ℕ`-only); the old
results are kept at the end as corollaries for `Span ℕ`.
-/

namespace CategoricalInterventionsProofs

variable {τ : Type*} [LinearOrder τ]

/-- A half-open span `[lo, hi)` with `lo < hi`, so that it is nonempty. -/
@[ext]
structure Span (τ : Type*) [LinearOrder τ] where
  lo : τ
  hi : τ
  lo_lt_hi : lo < hi

/-- An instant `{time}`: the support of a pulse. -/
@[ext]
structure Instant (τ : Type*) where
  time : τ

/-- A support is a span or an instant. -/
inductive Support (τ : Type*) [LinearOrder τ] where
  | span : Span τ → Support τ
  | instant : Instant τ → Support τ

namespace Span

/-- `t ∈ [lo, hi)`. -/
def mem (s : Span τ) (t : τ) : Prop := s.lo ≤ t ∧ t < s.hi

instance (s : Span τ) (t : τ) : Decidable (s.mem t) :=
  inferInstanceAs (Decidable (s.lo ≤ t ∧ t < s.hi))

/-- The set of times in the span, `Set.Ico lo hi`. -/
def memSet (s : Span τ) : Set τ := Set.Ico s.lo s.hi

@[simp] theorem mem_memSet {s : Span τ} {t : τ} : t ∈ s.memSet ↔ s.mem t := Iff.rfl

/-- Two spans overlap when each starts before the other ends. -/
def overlaps (s s' : Span τ) : Prop := s.lo < s'.hi ∧ s'.lo < s.hi

/-- Disjointness is the negation of overlap. -/
def Disjoint (s s' : Span τ) : Prop := ¬ s.overlaps s'

end Span

namespace Support

/-- Membership: a span contains `t` iff `lo ≤ t < hi`; an instant iff `t = t₀`. -/
def mem : Support τ → τ → Prop
  | .span s, t => s.lo ≤ t ∧ t < s.hi
  | .instant i, t => t = i.time

instance (S : Support τ) (t : τ) : Decidable (S.mem t) :=
  match S with
  | .span s => inferInstanceAs (Decidable (s.lo ≤ t ∧ t < s.hi))
  | .instant i => inferInstanceAs (Decidable (t = i.time))

/-- The set of times in the support. -/
def memSet (S : Support τ) : Set τ := {t | S.mem t}

@[simp] theorem mem_memSet {S : Support τ} {t : τ} : t ∈ S.memSet ↔ S.mem t := Iff.rfl

@[simp] theorem mem_span {s : Span τ} {t : τ} : (Support.span s).mem t ↔ s.mem t := Iff.rfl

@[simp] theorem mem_instant {i : Instant τ} {t : τ} :
    (Support.instant i).mem t ↔ t = i.time := Iff.rfl

/-- Whether the support is a span (as opposed to an instant). -/
def isSpan : Support τ → Prop
  | .span _ => True
  | .instant _ => False

instance (S : Support τ) : Decidable S.isSpan := by
  cases S <;> simp only [isSpan] <;> infer_instance

end Support

/-! ## Basic facts about spans -/

/-- The start time of a span belongs to it: interventions begin at `lo`. -/
theorem span_lo_mem (s : Span τ) : s.mem s.lo :=
  ⟨le_refl _, s.lo_lt_hi⟩

/-- The end time of a span does not belong to it: interventions lift at `hi`. -/
theorem span_hi_not_mem (s : Span τ) : ¬ s.mem s.hi :=
  fun h => lt_irrefl _ h.2

/-- Overlap is symmetric. -/
theorem overlaps_symm {s s' : Span τ} (h : s.overlaps s') : s'.overlaps s :=
  ⟨h.2, h.1⟩

/-- If one span ends before the other starts, they are disjoint. -/
theorem disjoint_of_hi_le_lo {s s' : Span τ} (h : s.hi ≤ s'.lo) : s.Disjoint s' :=
  fun ov => absurd ov.2 (not_lt_of_ge h)

/-- Two spans overlap iff some time lies in both. -/
theorem overlaps_iff_exists_mem {s s' : Span τ} :
    s.overlaps s' ↔ ∃ t, s.mem t ∧ s'.mem t := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨max s.lo s'.lo, ⟨le_max_left _ _, ?_⟩, ⟨le_max_right _ _, ?_⟩⟩
    · exact max_lt s.lo_lt_hi h₂
    · exact max_lt h₁ s'.lo_lt_hi
  · rintro ⟨t, ⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨lt_of_le_of_lt h₁ h₄, lt_of_le_of_lt h₃ h₂⟩

/-- Disjoint spans share no time. -/
theorem Span.Disjoint.not_mem {s s' : Span τ} (h : s.Disjoint s') {t : τ}
    (ht : s.mem t) : ¬ s'.mem t :=
  fun ht' => h (overlaps_iff_exists_mem.mpr ⟨t, ht, ht'⟩)

/-- Every support is order-convex (`Set.OrdConnected`): if `x ≤ y ≤ z` and `x, z`
are in the support then so is `y`.  This is the one property the sheaf and
cosheaf conditions on narratives use. -/
theorem support_ordConnected (S : Support τ) : S.memSet.OrdConnected := by
  cases S with
  | span s =>
    have : (Support.span s).memSet = Set.Ico s.lo s.hi := rfl
    rw [this]
    exact Set.ordConnected_Ico
  | instant i =>
    have : (Support.instant i).memSet = {i.time} := by
      ext t; simp [Support.memSet, Support.mem]
    rw [this]
    exact Set.ordConnected_singleton

/-- The intersection of two overlapping spans is again a span, namely
`[max lo lo', min hi hi')`. -/
theorem inter_span {s s' : Span τ} (h : s.overlaps s') :
    ∃ s'' : Span τ, s''.memSet = s.memSet ∩ s'.memSet := by
  refine ⟨⟨max s.lo s'.lo, min s.hi s'.hi, ?_⟩, ?_⟩
  · exact max_lt (lt_min s.lo_lt_hi h.1) (lt_min h.2 s'.lo_lt_hi)
  · ext t
    simp only [Span.memSet, Set.mem_Ico, Set.mem_inter_iff, max_le_iff, lt_min_iff]
    tauto

/-! ## Legacy corollaries (v0.1 `Interval.lean`, timeline `ℕ`) -/

/-- The v0.1 interval type: a span over `ℕ`. -/
abbrev Interval := Span ℕ

/-- v0.1 `Contains`. -/
abbrev Contains (I : Interval) (t : ℕ) : Prop := I.mem t

/-- v0.1 `Overlaps`. -/
abbrev Overlaps (I J : Interval) : Prop := I.overlaps J

/-- v0.1 `Disjoint`. -/
abbrev Disjoint (I J : Interval) : Prop := I.Disjoint J

theorem start_mem (I : Interval) : Contains I I.lo := span_lo_mem I

theorem stop_not_mem (I : Interval) : ¬ Contains I I.hi := span_hi_not_mem I

theorem disjoint_of_stop_le_start {I J : Interval} (h : I.hi ≤ J.lo) : Disjoint I J :=
  disjoint_of_hi_le_lo h

theorem no_overlap_of_disjoint {I J : Interval} (h : Disjoint I J) : ¬ Overlaps I J := h

end CategoricalInterventionsProofs
