import CategoricalInterventionsProofs.Program

/-!
# SA-Pass: shared glue lemmas

Small facts about the development's definitions that several shadow files use
as "glue" (they are about the definitions, not about any tested claim).  None
of them uses a target theorem; each is proved directly from the definitions.
-/

namespace CategoricalInterventionsProofs.SAPass

open CategoricalInterventionsProofs

universe u v w

variable {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]

/-- The fold of a two-atom program, by cases on activity. -/
theorem foldAt_pair (a b : Atom τ T M) (j : T) (t : τ) :
    foldAt j [a, b] t =
      if a.support.mem t ∧ a.target = j then
        (if b.support.mem t ∧ b.target = j then mul a.effect b.effect else some a.effect)
      else (if b.support.mem t ∧ b.target = j then some b.effect else some one) := by
  rw [foldAt_cons, foldAt_cons, foldAt_nil]
  by_cases ha : a.support.mem t ∧ a.target = j <;>
    by_cases hb : b.support.mem t ∧ b.target = j <;> simp [ha, hb, mul_one]

/-- A two-atom program is conflict-free iff the atoms combine whenever they are
co-active on a common target. -/
theorem conflictFree_pair_iff (a b : Atom τ T M) :
    ConflictFree [a, b] ↔
      ∀ t, a.support.mem t → b.support.mem t → a.target = b.target →
        (mul a.effect b.effect).isSome := by
  constructor
  · intro h t hta htb hj
    have := h t a.target
    rw [foldAt_pair] at this
    simpa [hta, htb, hj] using this
  · intro h t j
    rw [foldAt_pair]
    by_cases ha : a.support.mem t ∧ a.target = j <;>
      by_cases hb : b.support.mem t ∧ b.target = j <;> simp [ha, hb]
    exact h t ha.1 hb.1 (ha.2.trans hb.2.symm)

/-- The left factor of a conflict-free composite is conflict-free, for every
PCM (no pairwise hypothesis): the composite fold is `foldP.bind …`. -/
theorem conflictFree_of_append_left {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) :
    ConflictFree P := by
  intro t j
  have := h t j
  rw [foldAt_append] at this
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at this
  · rfl

/-- The right factor of a conflict-free composite is conflict-free, for every
PCM (no pairwise hypothesis). -/
theorem conflictFree_of_append_right {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) :
    ConflictFree Q := by
  intro t j
  have := h t j
  rw [foldAt_append] at this
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at this
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at this
    · rfl

/-- The natural-language pairwise relation: two atoms *combine* if, whenever
they share a target and a time, their effects have a defined product. -/
def Combines (a b : Atom τ T M) : Prop :=
  a.target = b.target → (∃ t, a.support.mem t ∧ b.support.mem t) →
    (mul a.effect b.effect).isSome

/-- `PairwiseCompatible` is the natural-language pairwise condition. -/
theorem pairwiseCompatible_iff_combines (P : Program τ T M) :
    PairwiseCompatible P ↔ P.Pairwise Combines := by
  constructor
  · intro h
    rw [List.pairwise_iff_forall_sublist]
    intro a b hab hj ⟨t, hta, htb⟩
    have hsub : [a, b].Sublist ((active P t).filter (fun x => decide (x.target = b.target))) := by
      have h1 : [a, b].Sublist (active P t) := by
        have := (hab.filter (fun x => decide (x.support.mem t)))
        simpa [active, hta, htb] using this
      have := h1.filter (fun x => decide (x.target = b.target))
      simpa [hj] using this
    exact List.pairwise_iff_forall_sublist.mp (h t b.target) hsub
  · intro h t j
    have h' := (h.filter (fun x => decide (x.support.mem t))).filter
      (fun x => decide (x.target = j))
    change ((active P t).filter _).Pairwise _
    refine h'.imp_of_mem ?_
    intro a b ha hb hab
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    exact hab (ha.2.trans hb.2.symm) ⟨t, ha.1.2, hb.1.2⟩

end CategoricalInterventionsProofs.SAPass
