import CategoricalInterventionsProofs.Support
import CategoricalInterventionsProofs.PCM

/-!
# Programs, active sets, conflict-freeness

An *atom* is `(id, target, support, effect)`; a *program* is a finite list of
atoms.  `active P t` is the sublist of atoms whose support contains `t`, and
`foldAt j P t` is the PCM product of the effects of active atoms on target `j`.
A program is *conflict-free* when every such fold is defined.

This file replaces the v0.1 `Composition.lean` and `Compatibility.lean`; their
results are kept as corollaries at the end.
-/

namespace CategoricalInterventionsProofs

variable {τ T M : Type*} [LinearOrder τ]

/-- An intervention atom: an identifier, a target, a support, and an effect. -/
structure Atom (τ T M : Type*) [LinearOrder τ] where
  id : ℕ
  target : T
  support : Support τ
  effect : M

/-- A program is a finite list of atoms. -/
abbrev Program (τ T M : Type*) [LinearOrder τ] := List (Atom τ T M)

/-- Raw program composition is list append. -/
def compose (P Q : Program τ T M) : Program τ T M := P ++ Q

infixl:65 " ⊕ᵢ " => compose

/-- The atoms of `P` in force at time `t`. -/
def active (P : Program τ T M) (t : τ) : Program τ T M :=
  P.filter (fun a => decide (a.support.mem t))

@[simp] theorem mem_active {P : Program τ T M} {t : τ} {a : Atom τ T M} :
    a ∈ active P t ↔ a ∈ P ∧ a.support.mem t := by
  simp [active]

/-- The effects of the active atoms of `P` on target `j` at time `t`. -/
def effectsAt [DecidableEq T] (j : T) (P : Program τ T M) (t : τ) : List M :=
  ((active P t).filter (fun a => decide (a.target = j))).map (·.effect)

/-- The PCM fold of the effects of the active atoms of `P` on target `j` at
time `t`; `none` means a conflict. -/
def foldAt [DecidableEq T] [PCM M] (j : T) (P : Program τ T M) (t : τ) : Option M :=
  foldList (effectsAt j P t)

/-- A program is conflict-free when every fold is defined. -/
def ConflictFree [DecidableEq T] [PCM M] (P : Program τ T M) : Prop :=
  ∀ (t : τ) (j : T), (foldAt j P t).isSome

/-! ## Composition laws (kept from v0.1) -/

/-- Raw program composition is associative. -/
theorem compose_assoc (P Q R : Program τ T M) : (P ⊕ᵢ Q) ⊕ᵢ R = P ⊕ᵢ (Q ⊕ᵢ R) :=
  List.append_assoc P Q R

/-- The empty program is a left identity. -/
theorem compose_nil_left (P : Program τ T M) : ([] : Program τ T M) ⊕ᵢ P = P := rfl

/-- The empty program is a right identity. -/
theorem compose_nil_right (P : Program τ T M) : P ⊕ᵢ ([] : Program τ T M) = P :=
  List.append_nil P

theorem compose_empty_left (P : Program τ T M) : ([] : Program τ T M) ⊕ᵢ P = P :=
  compose_nil_left P

theorem compose_empty_right (P : Program τ T M) : P ⊕ᵢ ([] : Program τ T M) = P :=
  compose_nil_right P

/-! ## Active sets and folds of composite programs -/

/-- The active set of a composite is the concatenation of the active sets. -/
theorem active_append (P Q : Program τ T M) (t : τ) :
    active (P ++ Q) t = active P t ++ active Q t := by
  simp [active, List.filter_append]

@[simp] theorem active_nil (t : τ) : active ([] : Program τ T M) t = [] := rfl

theorem active_cons (a : Atom τ T M) (P : Program τ T M) (t : τ) :
    active (a :: P) t = if a.support.mem t then a :: active P t else active P t := by
  by_cases h : a.support.mem t <;> simp [active, h]

section Effects
variable [DecidableEq T]

theorem effectsAt_append (j : T) (P Q : Program τ T M) (t : τ) :
    effectsAt j (P ++ Q) t = effectsAt j P t ++ effectsAt j Q t := by
  simp [effectsAt, active_append]

@[simp] theorem effectsAt_nil (j : T) (t : τ) : effectsAt j ([] : Program τ T M) t = [] := rfl

theorem effectsAt_cons (j : T) (a : Atom τ T M) (P : Program τ T M) (t : τ) :
    effectsAt j (a :: P) t =
      if a.support.mem t ∧ a.target = j then a.effect :: effectsAt j P t
      else effectsAt j P t := by
  simp only [effectsAt, active_cons]
  by_cases hm : a.support.mem t
  · by_cases hj : a.target = j
    · simp [hm, hj]
    · simp [hm, hj]
  · simp [hm]

/-- `effectsAt` of a sublist program is a sublist of the effects. -/
theorem effectsAt_sublist {P Q : Program τ T M} (h : P.Sublist Q) (j : T) (t : τ) :
    (effectsAt j P t).Sublist (effectsAt j Q t) :=
  ((h.filter _).filter _).map _

end Effects

section Fold
variable [DecidableEq T] [PCM M]

/-- The fold over a composite is the product of the folds. -/
theorem foldAt_append (j : T) (P Q : Program τ T M) (t : τ) :
    foldAt j (P ++ Q) t = (foldAt j P t).bind fun a => (foldAt j Q t).bind fun b => mul a b := by
  simp only [foldAt, effectsAt_append, foldList_append]

@[simp] theorem foldAt_nil (j : T) (t : τ) : foldAt j ([] : Program τ T M) t = some one := rfl

theorem foldAt_cons (j : T) (a : Atom τ T M) (P : Program τ T M) (t : τ) :
    foldAt j (a :: P) t =
      if a.support.mem t ∧ a.target = j then (foldAt j P t).bind fun b => mul a.effect b
      else foldAt j P t := by
  simp only [foldAt, effectsAt_cons]
  split_ifs <;> rfl

/-- Permuting a program does not change any fold (order irrelevance). -/
theorem foldAt_perm {P Q : Program τ T M} (h : P.Perm Q) (j : T) (t : τ) :
    foldAt j P t = foldAt j Q t := by
  unfold foldAt effectsAt active
  exact fold_perm (((h.filter _).filter _).map _)

/-- If no atom of `P` targets `j` at `t`, the fold is the unit. -/
theorem foldAt_eq_one_of_none (j : T) (P : Program τ T M) (t : τ)
    (h : ∀ a ∈ P, a.support.mem t → a.target ≠ j) : foldAt j P t = some one := by
  have : effectsAt j P t = [] := by
    simp only [effectsAt, List.map_eq_nil_iff, List.filter_eq_nil_iff, mem_active,
      decide_eq_true_eq]
    intro a ⟨ha, hm⟩
    exact h a ha hm
  simp [foldAt, this]

/-- If no atom of `P` is active at `t`, every fold is the unit. -/
theorem foldAt_eq_one_of_not_active (j : T) (P : Program τ T M) (t : τ)
    (h : ∀ a ∈ P, ¬ a.support.mem t) : foldAt j P t = some one :=
  foldAt_eq_one_of_none j P t (fun a ha hm => absurd hm (h a ha))

end Fold

/-! ## Conflict-freeness of composites -/

section Factors
variable [DecidableEq T] [PCM M]

/-- **Factors are conflict-free (left).** The left factor of a conflict-free
composite is conflict-free, for *every* PCM: by `foldAt_append` the composite
fold is `(foldAt j P t).bind …`, which is defined only if `foldAt j P t` is.
(No `PCMPairwise` hypothesis; SA-Pass gap G3.) -/
theorem conflictFree_append_left {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) :
    ConflictFree P := by
  intro t j
  have := h t j
  rw [foldAt_append] at this
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at this
  · rfl

/-- **Factors are conflict-free (right).** The right factor of a conflict-free
composite is conflict-free, for every PCM (no `PCMPairwise` hypothesis). -/
theorem conflictFree_append_right {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) :
    ConflictFree Q := by
  intro t j
  have := h t j
  rw [foldAt_append] at this
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at this
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at this
    · rfl

/-- Both factors of a conflict-free composite are conflict-free. -/
theorem conflictFree_of_append {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) :
    ConflictFree P ∧ ConflictFree Q :=
  ⟨conflictFree_append_left h, conflictFree_append_right h⟩

/-- **Separated composites.** If no atom of `P` and no atom of `Q` are ever
active at the same time on the same target, then `P ++ Q` is conflict-free iff
both factors are: at every `(t, j)` one of the two folds is the unit. -/
theorem conflictFree_append_iff_of_separated {P Q : Program τ T M}
    (hsep : ∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → b.support.mem t → a.target ≠ b.target) :
    ConflictFree (P ++ Q) ↔ ConflictFree P ∧ ConflictFree Q := by
  refine ⟨conflictFree_of_append, ?_⟩
  rintro ⟨hP, hQ⟩ t j
  rw [foldAt_append]
  by_cases hex : ∃ a ∈ P, a.support.mem t ∧ a.target = j
  · obtain ⟨a, ha, hta, hj⟩ := hex
    have hQ1 : foldAt j Q t = some one :=
      foldAt_eq_one_of_none j Q t (fun b hb htb e => hsep a ha b hb t hta htb (hj.trans e.symm))
    rw [hQ1]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hP t j)
    simp [hx, mul_one]
  · push Not at hex
    have hP1 : foldAt j P t = some one :=
      foldAt_eq_one_of_none j P t (fun a ha hta => hex a ha hta)
    rw [hP1]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hQ t j)
    simp [hy, one_mul]

end Factors

section ConflictFree
variable [DecidableEq T] [PCM M] [PCMPairwise M]

/-- A sublist of a conflict-free program is conflict-free (dropping atoms never
creates conflicts).  Requires the pairwise property of the PCM. -/
theorem conflictFree_sublist {P Q : Program τ T M} (h : P.Sublist Q)
    (hQ : ConflictFree Q) : ConflictFree P :=
  fun t j => foldList_sublist (effectsAt_sublist h j t) (hQ t j)

/-- Pairwise compatibility: every two active atoms on the same target have a
defined product.  This is what the `O(n²)` conflict check computes. -/
def PairwiseCompatible (P : Program τ T M) : Prop :=
  ∀ (t : τ) (j : T), ((active P t).filter (fun a => decide (a.target = j))).Pairwise
    (fun a b => (mul a.effect b.effect).isSome)

/-- **Pairwise suffices.** If all pairs of active same-target atoms are compatible
then the program is conflict-free. -/
theorem conflictFree_of_pairwise {P : Program τ T M} (h : PairwiseCompatible P) :
    ConflictFree P := by
  intro t j
  rw [foldAt, foldList_isSome_iff_pairwise, effectsAt, List.pairwise_map]
  exact h t j

/-- Conversely, a conflict-free program is pairwise compatible. -/
theorem pairwise_of_conflictFree {P : Program τ T M} (h : ConflictFree P) :
    PairwiseCompatible P := by
  intro t j
  have := h t j
  rwa [foldAt, foldList_isSome_iff_pairwise, effectsAt, List.pairwise_map] at this

theorem conflictFree_iff_pairwise (P : Program τ T M) :
    ConflictFree P ↔ PairwiseCompatible P :=
  ⟨pairwise_of_conflictFree, conflictFree_of_pairwise⟩

end ConflictFree

/-! ## Two-atom programs (v0.1 `Compatibility.lean`, now corollaries) -/

section Pair
variable [DecidableEq T] [PCM M]

/-- A two-atom program is conflict-free provided the two atoms are compatible
whenever they are simultaneously active on the same target. -/
theorem conflictFree_pair {a b : Atom τ T M}
    (h : ∀ t, a.support.mem t → b.support.mem t → a.target = b.target →
      (mul a.effect b.effect).isSome) :
    ConflictFree [a, b] := by
  intro t j
  rw [foldAt_cons, foldAt_cons, foldAt_nil]
  by_cases ha : a.support.mem t ∧ a.target = j <;>
    by_cases hb : b.support.mem t ∧ b.target = j <;> simp [ha, hb, mul_one]
  exact h t ha.1 hb.1 (ha.2.trans hb.2.symm)

/-- Two atoms on different targets never conflict. -/
theorem different_target_compatible {a b : Atom τ T M} (h : a.target ≠ b.target) :
    ConflictFree [a, b] :=
  conflictFree_pair (fun _ _ _ hj => absurd hj h)

/-- **Disjoint supports never conflict**, for arbitrary supports (spans or
instants): two atoms that are never simultaneously active are conflict-free,
whatever their targets and effects.  (SA-Pass gap G2.) -/
theorem disjoint_compatible' {a b : Atom τ T M}
    (h : ∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) : ConflictFree [a, b] :=
  conflictFree_pair (fun t hta htb _ => absurd ⟨hta, htb⟩ (h t))

/-- Two atoms with disjoint span supports never conflict (corollary of
`disjoint_compatible'`). -/
theorem disjoint_compatible {a b : Atom τ T M} {s s' : Span τ}
    (ha : a.support = .span s) (hb : b.support = .span s') (h : s.Disjoint s') :
    ConflictFree [a, b] :=
  disjoint_compatible' (fun t ⟨hta, htb⟩ => by
    rw [ha] at hta
    rw [hb] at htb
    exact absurd htb (h.not_mem hta))

end Pair

end CategoricalInterventionsProofs
