import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Narrative

/-!
# SA-Pass claim 10

NL claim: **"A program is a persistent narrative (sheaf): A[a,b] = A[a,p] ∩ A[p,b]."**
Targets: `persistent_glue`, `persistent_antitone`.
-/

namespace CategoricalInterventionsProofs.SAPass.C10

open CategoricalInterventionsProofs
open Classical

universe u v w

/-! ## Shadows for `persistent_glue` -/

/-- NL: "A[a,b] = A[a,p] ∩ A[p,b]" — as an equality of the *sets* of atoms. -/
theorem sh_pg_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) :
    {x | x ∈ persistent P (Set.Icc a b)} =
      {x | x ∈ persistent P (Set.Icc a p)} ∩ {x | x ∈ persistent P (Set.Icc p b)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_persistent]
  rw [← Set.Icc_union_Icc_eq_Icc hap hpb, Set.union_subset_iff]
  tauto

/-- NL: "A[a,b] = A[a,p] ∩ A[p,b]" — as an equality of atom *lists*, with `∩`
read as "those atoms of A[a,p] that also lie in A[p,b]". -/
theorem sh_pg_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) :
    persistent P (Set.Icc a b) =
      (persistent P (Set.Icc a p)).filter (fun x => decide (x ∈ persistent P (Set.Icc p b))) := by
  simp only [persistent, List.filter_filter]
  apply List.filter_congr
  intro x hx
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_filter, hx, true_and]
  rw [← Set.Icc_union_Icc_eq_Icc hap hpb, Set.union_subset_iff]
  tauto

/-- NL facet (iterated gluing): a chain `a ≤ p₁ ≤ p₂ ≤ b` glues in three pieces. -/
theorem sh_pg_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p₁ p₂ b : τ) (h₁ : a ≤ p₁) (h₂ : p₁ ≤ p₂) (h₃ : p₂ ≤ b) (x : Atom τ T M) :
    x ∈ persistent P (Set.Icc a b) ↔
      x ∈ persistent P (Set.Icc a p₁) ∧ x ∈ persistent P (Set.Icc p₁ p₂) ∧
        x ∈ persistent P (Set.Icc p₂ b) := by
  simp only [mem_persistent]
  rw [← Set.Icc_union_Icc_eq_Icc (le_trans h₁ h₂) h₃, ← Set.Icc_union_Icc_eq_Icc h₁ h₂,
    Set.union_subset_iff, Set.union_subset_iff]
  tauto

sa_check_shadow_free sh_pg_1 [persistent_glue, persistent_antitone]
sa_check_shadow_free sh_pg_2 [persistent_glue, persistent_antitone]
sa_check_shadow_free sh_pg_3 [persistent_glue, persistent_antitone]

theorem fwd_pg_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p) ∧ x ∈ persistent P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ persistent P (Set.Icc a b)} =
        {x | x ∈ persistent P (Set.Icc a p)} ∩ {x | x ∈ persistent P (Set.Icc p b)} := by
  intro τ T M _ P a p b hap hpb
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact hT hap hpb

sa_check_fwd fwd_pg_1 persistent_glue sh_pg_1 forbid [persistent_antitone, sh_pg_2, sh_pg_3]

theorem fwd_pg_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p) ∧ x ∈ persistent P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      persistent P (Set.Icc a b) =
        (persistent P (Set.Icc a p)).filter (fun x => decide (x ∈ persistent P (Set.Icc p b))) := by
  intro τ T M _ P a p b hap hpb
  have key : ∀ x ∈ P, (Set.Icc a b ⊆ x.support.memSet ↔
      Set.Icc a p ⊆ x.support.memSet ∧ Set.Icc p b ⊆ x.support.memSet) := by
    intro x hx
    have h := @hT τ T M _ P a p b hap hpb x
    simp only [mem_persistent, hx, true_and] at h
    exact h
  simp only [persistent, List.filter_filter]
  apply List.filter_congr
  intro x hx
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_filter, hx, true_and]
  rw [key x hx]
  tauto

sa_check_fwd fwd_pg_2 persistent_glue sh_pg_2 forbid [persistent_antitone, sh_pg_1, sh_pg_3]

theorem fwd_pg_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p) ∧ x ∈ persistent P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p₁ p₂ b : τ), a ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ b → ∀ (x : Atom τ T M),
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p₁) ∧ x ∈ persistent P (Set.Icc p₁ p₂) ∧
          x ∈ persistent P (Set.Icc p₂ b) := by
  intro τ T M _ P a p₁ p₂ b h₁ h₂ h₃ x
  rw [hT (le_trans h₁ h₂) h₃, hT h₁ h₂, and_assoc]

sa_check_fwd fwd_pg_3 persistent_glue sh_pg_3 forbid [persistent_antitone, sh_pg_1, sh_pg_2]

theorem bwd_pg
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ persistent P (Set.Icc a b)} =
        {x | x ∈ persistent P (Set.Icc a p)} ∩ {x | x ∈ persistent P (Set.Icc p b)})
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      persistent P (Set.Icc a b) =
        (persistent P (Set.Icc a p)).filter (fun x => decide (x ∈ persistent P (Set.Icc p b))))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p₁ p₂ b : τ), a ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ b → ∀ (x : Atom τ T M),
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p₁) ∧ x ∈ persistent P (Set.Icc p₁ p₂) ∧
          x ∈ persistent P (Set.Icc p₂ b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ persistent P (Set.Icc a b) ↔
        x ∈ persistent P (Set.Icc a p) ∧ x ∈ persistent P (Set.Icc p b) := by
  intro τ T M _ P a p b hap hpb x
  have _ := @h₂
  have _ := @h₃
  have := Set.ext_iff.mp (h₁ P a p b hap hpb) x
  simpa only [Set.mem_setOf_eq, Set.mem_inter_iff] using this

sa_check_bwd bwd_pg persistent_glue [sh_pg_1, sh_pg_2, sh_pg_3] forbid [persistent_antitone]

/-! ## Shadows for `persistent_antitone` -/

/-- NL: "(sheaf)" — restriction: the atoms in force throughout a larger interval
are among those in force throughout a smaller one (list inclusion). -/
theorem sh_pa_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (I J : Set τ) (h : I ⊆ J) : persistent P J ⊆ persistent P I := by
  intro x hx
  rw [mem_persistent] at *
  exact ⟨hx.1, h.trans hx.2⟩

/-- NL facet: for closed intervals, shrinking the interval keeps every atom. -/
theorem sh_pa_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a b a' b' : τ) (ha : a ≤ a') (hb : b' ≤ b) (x : Atom τ T M)
    (hx : x ∈ persistent P (Set.Icc a b)) : x ∈ persistent P (Set.Icc a' b') :=
  sh_pa_1 P _ _ (Set.Icc_subset_Icc ha hb) hx

/-- NL facet: restriction is even a sublist (order of atoms preserved). -/
theorem sh_pa_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (I J : Set τ) (h : I ⊆ J) : (persistent P J).Sublist (persistent P I) := by
  have : persistent P J = (persistent P I).filter (fun x => decide (J ⊆ x.support.memSet)) := by
    simp only [persistent, List.filter_filter]
    apply List.filter_congr
    intro x _
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun hJ => ⟨hJ, h.trans hJ⟩, fun hh => hh.1⟩
  rw [this]
  exact List.filter_sublist

sa_check_shadow_free sh_pa_1 [persistent_glue, persistent_antitone]
sa_check_shadow_free sh_pa_2 [persistent_glue, persistent_antitone]
sa_check_shadow_free sh_pa_3 [persistent_glue, persistent_antitone]

theorem fwd_pa_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ persistent P J → x ∈ persistent P I) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → persistent P J ⊆ persistent P I := by
  intro τ T M _ P I J h x hx
  exact hT h hx

sa_check_fwd fwd_pa_1 persistent_antitone sh_pa_1 forbid [persistent_glue, sh_pa_2, sh_pa_3]

theorem fwd_pa_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ persistent P J → x ∈ persistent P I) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a b a' b' : τ), a ≤ a' → b' ≤ b → ∀ (x : Atom τ T M),
      x ∈ persistent P (Set.Icc a b) → x ∈ persistent P (Set.Icc a' b') := by
  intro τ T M _ P a b a' b' ha hb x hx
  exact hT (Set.Icc_subset_Icc ha hb) hx

sa_check_fwd fwd_pa_2 persistent_antitone sh_pa_2 forbid [persistent_glue, sh_pa_1, sh_pa_3]

theorem fwd_pa_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ persistent P J → x ∈ persistent P I) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → (persistent P J).Sublist (persistent P I) := by
  intro τ T M _ P I J h
  have key : ∀ x ∈ P, J ⊆ x.support.memSet → I ⊆ x.support.memSet := by
    intro x hx hJ
    exact (mem_persistent.mp (hT h (mem_persistent.mpr ⟨hx, hJ⟩))).2
  have : persistent P J = (persistent P I).filter (fun x => decide (J ⊆ x.support.memSet)) := by
    simp only [persistent, List.filter_filter]
    apply List.filter_congr
    intro x hx
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun hJ => ⟨hJ, key x hx hJ⟩, fun hh => hh.1⟩
  rw [this]
  exact List.filter_sublist

sa_check_fwd fwd_pa_3 persistent_antitone sh_pa_3 forbid [persistent_glue, sh_pa_1, sh_pa_2]

theorem bwd_pa
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → persistent P J ⊆ persistent P I)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a b a' b' : τ), a ≤ a' → b' ≤ b → ∀ (x : Atom τ T M),
      x ∈ persistent P (Set.Icc a b) → x ∈ persistent P (Set.Icc a' b'))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → (persistent P J).Sublist (persistent P I)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ persistent P J → x ∈ persistent P I := by
  intro τ T M _ P I J h x hx
  have _ := @h₂
  have _ := @h₃
  exact h₁ P I J h hx

sa_check_bwd bwd_pa persistent_antitone [sh_pa_1, sh_pa_2, sh_pa_3] forbid [persistent_glue]

end CategoricalInterventionsProofs.SAPass.C10
