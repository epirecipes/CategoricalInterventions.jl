import CategoricalInterventionsProofs.Program

/-!
# Narratives: programs as sheaves and cosheaves on closed intervals

For a closed interval `I = [a, b]` (allowing `a = b`), the *persistent
narrative* `persistent P I` is the list of atoms in force throughout `I`, and
the *cumulative narrative* `cumulative P I` is the list of atoms in force at
some time of `I`.  The persistent narrative is contravariant and satisfies the
sheaf (gluing) condition; the cumulative narrative is covariant and satisfies
the cosheaf conditions, the second of which uses convexity of supports.
-/

namespace CategoricalInterventionsProofs

open Classical

variable {τ T M : Type*} [LinearOrder τ]

/-- The atoms of `P` in force throughout `I`. -/
noncomputable def persistent (P : Program τ T M) (I : Set τ) : Program τ T M :=
  P.filter (fun a => decide (I ⊆ a.support.memSet))

/-- The atoms of `P` in force at some time of `I`. -/
noncomputable def cumulative (P : Program τ T M) (I : Set τ) : Program τ T M :=
  P.filter (fun a => decide (I ∩ a.support.memSet).Nonempty)

@[simp] theorem mem_persistent {P : Program τ T M} {I : Set τ} {x : Atom τ T M} :
    x ∈ persistent P I ↔ x ∈ P ∧ I ⊆ x.support.memSet := by
  simp [persistent]

@[simp] theorem mem_cumulative {P : Program τ T M} {I : Set τ} {x : Atom τ T M} :
    x ∈ cumulative P I ↔ x ∈ P ∧ (I ∩ x.support.memSet).Nonempty := by
  simp [cumulative]

/-- The persistent narrative is contravariant: an atom in force throughout a
larger interval is in force throughout any sub-interval. -/
theorem persistent_antitone {P : Program τ T M} {I J : Set τ} (h : I ⊆ J) {x : Atom τ T M}
    (hx : x ∈ persistent P J) : x ∈ persistent P I := by
  rw [mem_persistent] at *
  exact ⟨hx.1, h.trans hx.2⟩

/-- The cumulative narrative is covariant. -/
theorem cumulative_monotone {P : Program τ T M} {I J : Set τ} (h : I ⊆ J) {x : Atom τ T M}
    (hx : x ∈ cumulative P I) : x ∈ cumulative P J := by
  rw [mem_cumulative] at *
  exact ⟨hx.1, hx.2.mono (Set.inter_subset_inter_left _ h)⟩

/-- **Sheaf condition.** An atom is in force throughout `[a, b]` iff it is in force
throughout `[a, p]` and throughout `[p, b]`. -/
theorem persistent_glue {P : Program τ T M} {a p b : τ} (hap : a ≤ p) (hpb : p ≤ b)
    {x : Atom τ T M} :
    x ∈ persistent P (Set.Icc a b) ↔
      x ∈ persistent P (Set.Icc a p) ∧ x ∈ persistent P (Set.Icc p b) := by
  simp only [mem_persistent]
  rw [← Set.Icc_union_Icc_eq_Icc hap hpb, Set.union_subset_iff]
  tauto

/-- **Cosheaf condition (union).** An atom is in force at some time of `[a, b]` iff
at some time of `[a, p]` or of `[p, b]`. -/
theorem cumulative_union {P : Program τ T M} {a p b : τ} (hap : a ≤ p) (hpb : p ≤ b)
    {x : Atom τ T M} :
    x ∈ cumulative P (Set.Icc a b) ↔
      x ∈ cumulative P (Set.Icc a p) ∨ x ∈ cumulative P (Set.Icc p b) := by
  simp only [mem_cumulative]
  rw [← Set.Icc_union_Icc_eq_Icc hap hpb, Set.union_inter_distrib_right, Set.union_nonempty]
  tauto

/-- **Cosheaf condition (intersection).** By convexity of supports, an atom in force
at some time of `[a, p]` and at some time of `[p, b]` is in force at `p`. -/
theorem cumulative_inter_eq_point {P : Program τ T M} {a p b : τ} (hap : a ≤ p) (hpb : p ≤ b)
    {x : Atom τ T M} :
    x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) ↔
      x ∈ cumulative P (Set.Icc p p) := by
  simp only [mem_cumulative]
  constructor
  · rintro ⟨⟨hx, u, ⟨hu1, hu2⟩, hu⟩, ⟨-, w, ⟨hw1, hw2⟩, hw⟩⟩
    refine ⟨hx, p, ⟨le_refl _, le_refl _⟩, ?_⟩
    exact (support_ordConnected x.support).out hu hw ⟨hu2, hw1⟩
  · rintro ⟨hx, u, ⟨hu1, hu2⟩, hu⟩
    have : u = p := le_antisymm hu2 hu1
    subst this
    exact ⟨⟨hx, u, ⟨hap, le_refl _⟩, hu⟩, ⟨hx, u, ⟨le_refl _, hpb⟩, hu⟩⟩

/-- On a point interval, the persistent narrative is the active set. -/
theorem persistent_eq_active_of_point {P : Program τ T M} {t : τ} {x : Atom τ T M} :
    x ∈ persistent P (Set.Icc t t) ↔ x ∈ active P t := by
  simp [Set.Icc_self, Set.singleton_subset_iff]

/-- On a point interval, the cumulative narrative is also the active set. -/
theorem cumulative_eq_active_of_point {P : Program τ T M} {t : τ} {x : Atom τ T M} :
    x ∈ cumulative P (Set.Icc t t) ↔ x ∈ active P t := by
  simp [Set.Icc_self, Set.singleton_inter_nonempty]

end CategoricalInterventionsProofs
