import CategoricalInterventionsProofs.Semantics
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Shift and sequential composition

A program can be *shifted* in time by `δ`: every span `[lo, hi)` becomes
`[lo + δ, hi + δ)` and every instant `t₀` becomes `t₀ + δ` (the Julia
`shift(program, δ)`).  This needs the timeline to be an ordered additive group
(`ℝ`, `ℤ`, `ℚ`; Mathlib: `[AddCommGroup τ] [LinearOrder τ] [IsOrderedAddMonoid τ]`).

*Sequential composition* `seq P Q δ := P ++ shift δ Q` composes `P` with `Q`
delayed by `δ`.  The Julia `seq(p, q; gap)` computes `δ` from the extents of
`p` and `q` (`δ = extent(p)[2] + gap − extent(q)[1]`) so that `q` begins when
`p` ends; here `δ` is an explicit argument, which is all the laws need
(`seq` inherits the laws of `++` and `shift` for *every* `δ`).

Theorems: `shift_zero`, `shift_add`, `shift_append` (shift is an action of the
group `τ` by monoid endomorphisms of `(Program, ++)`), `mem_shift`,
`active_shift`, `foldAt_shift` (the shifted program at `t` is the original at
`t − δ`), `conflictFree_shift`, `apply_shift` (the action translates the
schedule), and for `seq`: `seq_assoc`, `seq_nil_left`, `seq_nil_right`,
`conflictFree_of_seq`, `seq_disjoint_conflictFree`, `apply_seq`.
-/

namespace CategoricalInterventionsProofs

variable {τ T M V : Type*}

/-! ## Shifting supports and atoms -/

section Instant
variable [AddCommGroup τ]

/-- Shift an instant by `δ`. -/
def Instant.shift (δ : τ) (i : Instant τ) : Instant τ := ⟨i.time + δ⟩

@[simp] theorem Instant.shift_time (δ : τ) (i : Instant τ) : (i.shift δ).time = i.time + δ := rfl

theorem Instant.shift_zero (i : Instant τ) : i.shift 0 = i := by
  ext; simp

theorem Instant.shift_add (δ₁ δ₂ : τ) (i : Instant τ) :
    (i.shift δ₂).shift δ₁ = i.shift (δ₁ + δ₂) := by
  ext; simp [add_assoc, add_comm δ₂ δ₁]

end Instant

variable [AddCommGroup τ] [LinearOrder τ] [IsOrderedAddMonoid τ]

/-- Shift a span by `δ`: `[lo, hi) ↦ [lo + δ, hi + δ)`. -/
def Span.shift (δ : τ) (s : Span τ) : Span τ :=
  ⟨s.lo + δ, s.hi + δ, (add_lt_add_iff_right δ).mpr s.lo_lt_hi⟩

/-- Shift a support by `δ`. -/
def Support.shift (δ : τ) : Support τ → Support τ
  | .span s => .span (s.shift δ)
  | .instant i => .instant (i.shift δ)

/-- Shift an atom by `δ` (id, target and effect unchanged). -/
def Atom.shift (δ : τ) (a : Atom τ T M) : Atom τ T M :=
  ⟨a.id, a.target, a.support.shift δ, a.effect⟩

/-- Shift a program by `δ`: shift every atom. -/
def shift (δ : τ) (P : Program τ T M) : Program τ T M := P.map (Atom.shift δ)

/-- Sequential composition: `P`, then `Q` delayed by `δ`. -/
def seq (P Q : Program τ T M) (δ : τ) : Program τ T M := P ++ shift δ Q

@[simp] theorem Span.shift_lo (δ : τ) (s : Span τ) : (s.shift δ).lo = s.lo + δ := rfl
@[simp] theorem Span.shift_hi (δ : τ) (s : Span τ) : (s.shift δ).hi = s.hi + δ := rfl
@[simp] theorem Support.shift_span (δ : τ) (s : Span τ) :
    (Support.span s).shift δ = .span (s.shift δ) := rfl
@[simp] theorem Support.shift_instant (δ : τ) (i : Instant τ) :
    (Support.instant i).shift δ = .instant (i.shift δ) := rfl
@[simp] theorem Atom.shift_id (δ : τ) (a : Atom τ T M) : (a.shift δ).id = a.id := rfl
@[simp] theorem Atom.shift_target (δ : τ) (a : Atom τ T M) : (a.shift δ).target = a.target := rfl
@[simp] theorem Atom.shift_support (δ : τ) (a : Atom τ T M) :
    (a.shift δ).support = a.support.shift δ := rfl
@[simp] theorem Atom.shift_effect (δ : τ) (a : Atom τ T M) : (a.shift δ).effect = a.effect := rfl

/-! ## The group action laws -/

theorem Span.shift_zero (s : Span τ) : s.shift 0 = s := by
  ext <;> simp

theorem Span.shift_add (δ₁ δ₂ : τ) (s : Span τ) : (s.shift δ₂).shift δ₁ = s.shift (δ₁ + δ₂) := by
  ext <;> simp [add_assoc, add_comm δ₂ δ₁]

theorem Support.shift_zero (S : Support τ) : S.shift 0 = S := by
  cases S with
  | span s => simp [Span.shift_zero]
  | instant i => simp [Instant.shift_zero]

theorem Support.shift_add (δ₁ δ₂ : τ) (S : Support τ) :
    (S.shift δ₂).shift δ₁ = S.shift (δ₁ + δ₂) := by
  cases S with
  | span s => simp [Span.shift_add]
  | instant i => simp [Instant.shift_add]

theorem Atom.shift_zero (a : Atom τ T M) : a.shift 0 = a := by
  cases a; simp [Atom.shift, Support.shift_zero]

theorem Atom.shift_add (δ₁ δ₂ : τ) (a : Atom τ T M) :
    (a.shift δ₂).shift δ₁ = a.shift (δ₁ + δ₂) := by
  cases a; simp [Atom.shift, Support.shift_add]

@[simp] theorem shift_nil (δ : τ) : shift δ ([] : Program τ T M) = [] := rfl

theorem shift_cons (δ : τ) (a : Atom τ T M) (P : Program τ T M) :
    shift δ (a :: P) = a.shift δ :: shift δ P := rfl

/-- **Shift by zero** is the identity. -/
theorem shift_zero (P : Program τ T M) : shift 0 P = P := by
  induction P with
  | nil => rfl
  | cons a P ih => rw [shift_cons, Atom.shift_zero, ih]

/-- **Shifts compose**: shifting by `δ₂` then `δ₁` is shifting by `δ₁ + δ₂`. -/
theorem shift_add (δ₁ δ₂ : τ) (P : Program τ T M) :
    shift δ₁ (shift δ₂ P) = shift (δ₁ + δ₂) P := by
  induction P with
  | nil => rfl
  | cons a P ih => rw [shift_cons, shift_cons, shift_cons, Atom.shift_add, ih]

/-- **Shift commutes with composition**: `shift δ (P ++ Q) = shift δ P ++ shift δ Q`. -/
theorem shift_append (δ : τ) (P Q : Program τ T M) :
    shift δ (P ++ Q) = shift δ P ++ shift δ Q :=
  List.map_append ..

theorem mem_shift_iff {δ : τ} {P : Program τ T M} {b : Atom τ T M} :
    b ∈ shift δ P ↔ ∃ a ∈ P, b = a.shift δ := by
  simp only [shift, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-! ## Membership and activity -/

/-- **Membership in a shifted support**: `t ∈ S + δ ↔ t − δ ∈ S`. -/
theorem Support.mem_shift (δ : τ) (S : Support τ) (t : τ) :
    (S.shift δ).mem t ↔ S.mem (t - δ) := by
  cases S with
  | span s =>
    simp only [Support.shift_span, Support.mem_span, Span.mem, Span.shift_lo, Span.shift_hi]
    rw [le_sub_iff_add_le, sub_lt_iff_lt_add]
  | instant i =>
    simp only [Support.shift_instant, Support.mem_instant, Instant.shift_time]
    rw [sub_eq_iff_eq_add]

/-- **Membership for a shifted atom**: the shifted atom is active at `t` iff the
original is active at `t − δ`. -/
theorem mem_shift (δ : τ) (a : Atom τ T M) (t : τ) :
    (a.shift δ).support.mem t ↔ a.support.mem (t - δ) :=
  Support.mem_shift δ a.support t

/-- **Activity translates**: the active set of the shifted program at `t` is the
shifted active set of the original at `t − δ`. -/
theorem active_shift (δ : τ) (P : Program τ T M) (t : τ) :
    active (shift δ P) t = (active P (t - δ)).map (Atom.shift δ) := by
  simp only [active, shift, List.filter_map]
  congr 1
  apply List.filter_congr
  intro a _
  simp only [Function.comp, mem_shift]

section Fold
variable [DecidableEq T] [PCM M]

omit [PCM M] in
theorem effectsAt_shift (δ : τ) (j : T) (P : Program τ T M) (t : τ) :
    effectsAt j (shift δ P) t = effectsAt j P (t - δ) := by
  simp only [effectsAt, active_shift, List.filter_map, List.map_map]
  congr 1

/-- **Folds translate**: the fold of the shifted program at `t` is the fold of the
original at `t − δ`. -/
theorem foldAt_shift (δ : τ) (j : T) (P : Program τ T M) (t : τ) :
    foldAt j (shift δ P) t = foldAt j P (t - δ) := by
  simp only [foldAt, effectsAt_shift]

/-- **Shift preserves and reflects conflict-freeness.** -/
theorem conflictFree_shift (δ : τ) (P : Program τ T M) :
    ConflictFree (shift δ P) ↔ ConflictFree P := by
  constructor
  · intro h t j
    have := h (t + δ) j
    rwa [foldAt_shift, add_sub_cancel_right] at this
  · intro h t j
    rw [foldAt_shift]
    exact h (t - δ) j

end Fold

/-! ## The action of a shifted program -/

section Apply
variable [DecidableEq T] [PCM M] [HasAct M V]

/-- **Shift translates the schedule.** The shifted program at time `t` sees what
the original sees at `t − δ`, applied to the baseline value at `t`:
`(shift δ P ▷ θ) t j = (P ▷ (s ↦ θ (s + δ))) (t − δ) j`. -/
theorem apply_shift (δ : τ) (P : Program τ T M) (θ : τ → T → V) (t : τ) (j : T) :
    apply (shift δ P) θ t j = apply P (fun s j => θ (s + δ) j) (t - δ) j := by
  simp only [apply, foldAt_shift, sub_add_cancel]

/-- `apply_shift` as an equality of schedules. -/
theorem apply_shift' (δ : τ) (P : Program τ T M) (θ : τ → T → V) :
    apply (shift δ P) θ = fun t => apply P (fun s => θ (s + δ)) (t - δ) := by
  funext t j
  exact apply_shift δ P θ t j

/-- Translating the baseline with the program translates the output:
`(shift δ P ▷ (s ↦ θ (s − δ))) (t + δ) = (P ▷ θ) t`. -/
theorem apply_shift_translate (δ : τ) (P : Program τ T M) (θ : τ → T → V) (t : τ) :
    apply (shift δ P) (fun s => θ (s - δ)) (t + δ) = apply P θ t := by
  funext j
  simp only [apply, foldAt_shift, add_sub_cancel_right]

end Apply

/-! ## Sequential composition -/

/-- **Sequence is associative** (with the delays adding up):
`seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁`. -/
theorem seq_assoc (P Q R : Program τ T M) (δ₁ δ₂ : τ) :
    seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁ := by
  simp only [seq, shift_append, shift_add, List.append_assoc]

/-- The empty program is a left unit for `seq` up to the shift of the second
factor: `seq [] Q δ = shift δ Q`. -/
theorem seq_nil_left (Q : Program τ T M) (δ : τ) : seq [] Q δ = shift δ Q := rfl

/-- The empty program is a right unit for `seq`: `seq P [] δ = P`. -/
theorem seq_nil_right (P : Program τ T M) (δ : τ) : seq P [] δ = P :=
  List.append_nil P

/-- `seq` with zero delay is plain composition. -/
theorem seq_zero (P Q : Program τ T M) : seq P Q 0 = P ⊕ᵢ Q := by
  simp [seq, compose, shift_zero]

section SeqFold
variable [DecidableEq T] [PCM M]

/-- **Factors of a conflict-free sequence are conflict-free**, unconditionally
(`Q` unshifted, since shift reflects conflict-freeness). -/
theorem conflictFree_of_seq {P Q : Program τ T M} {δ : τ} (h : ConflictFree (seq P Q δ)) :
    ConflictFree P ∧ ConflictFree Q :=
  ⟨conflictFree_append_left h, (conflictFree_shift δ Q).mp (conflictFree_append_right h)⟩

/-- **Conflict-freeness of a separated sequence.** If no atom of `P` and no
*shifted* atom of `Q` are ever active at the same time on the same target (the
situation `seq` is designed for: `Q` starts after `P` ends), then the sequence is
conflict-free iff both factors are.  Without the separation hypothesis the `←`
direction fails (overlap after shifting can create conflicts). -/
theorem seq_disjoint_conflictFree {P Q : Program τ T M} {δ : τ}
    (hsep : ∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t →
      a.target ≠ b.target) :
    ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q := by
  rw [seq, conflictFree_append_iff_of_separated, conflictFree_shift]
  intro a ha b hb t hta htb
  obtain ⟨b₀, hb₀, rfl⟩ := mem_shift_iff.mp hb
  exact hsep a ha b₀ hb₀ t hta htb

end SeqFold

/-- **Sequence acts as `P` then the delayed `Q`** (for acting PCMs and a
conflict-free sequence): `seq P Q δ ▷ θ = shift δ Q ▷ (P ▷ θ)`. -/
theorem apply_seq [DecidableEq T] [PCM M] [PCMAction M V] {P Q : Program τ T M} {δ : τ}
    (h : ConflictFree (seq P Q δ)) (θ : τ → T → V) :
    apply (seq P Q δ) θ = apply (shift δ Q) (apply P θ) :=
  apply_append h θ

end CategoricalInterventionsProofs
