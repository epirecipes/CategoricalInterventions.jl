import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Narrative

/-!
# SA-Pass claim 11

NL claim: **"A program is a cumulative narrative (cosheaf): C[a,b] = C[a,p] ∪ C[p,b]
and C[a,p] ∩ C[p,b] = C[p,p]."**
Targets: `cumulative_union`, `cumulative_inter_eq_point`, `cumulative_monotone`.
-/

namespace CategoricalInterventionsProofs.SAPass.C11

open CategoricalInterventionsProofs
open Classical

universe u v w

/-! ## Shadows for `cumulative_union` -/

/-- NL: "C[a,b] = C[a,p] ∪ C[p,b]" — as an equality of sets of atoms. -/
theorem sh_cu_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) :
    {x | x ∈ cumulative P (Set.Icc a b)} =
      {x | x ∈ cumulative P (Set.Icc a p)} ∪ {x | x ∈ cumulative P (Set.Icc p b)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, mem_cumulative]
  rw [← Set.Icc_union_Icc_eq_Icc hap hpb, Set.union_inter_distrib_right, Set.union_nonempty]
  tauto

/-- NL facet (iterated): a chain `a ≤ p₁ ≤ p₂ ≤ b` splits into three pieces. -/
theorem sh_cu_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p₁ p₂ b : τ) (h₁ : a ≤ p₁) (h₂ : p₁ ≤ p₂) (h₃ : p₂ ≤ b) (x : Atom τ T M) :
    x ∈ cumulative P (Set.Icc a b) ↔
      x ∈ cumulative P (Set.Icc a p₁) ∨ x ∈ cumulative P (Set.Icc p₁ p₂) ∨
        x ∈ cumulative P (Set.Icc p₂ b) := by
  simp only [mem_cumulative]
  rw [← Set.Icc_union_Icc_eq_Icc (le_trans h₁ h₂) h₃, ← Set.Icc_union_Icc_eq_Icc h₁ h₂,
    Set.union_inter_distrib_right, Set.union_inter_distrib_right, Set.union_nonempty,
    Set.union_nonempty]
  tauto

/-- NL facet: each piece embeds in the whole. -/
theorem sh_cu_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) (x : Atom τ T M) :
    (x ∈ cumulative P (Set.Icc a p) → x ∈ cumulative P (Set.Icc a b)) ∧
      (x ∈ cumulative P (Set.Icc p b) → x ∈ cumulative P (Set.Icc a b)) := by
  simp only [mem_cumulative]
  constructor
  · rintro ⟨hx, u, ⟨hu1, hu2⟩, hu⟩
    exact ⟨hx, u, ⟨hu1, le_trans hu2 hpb⟩, hu⟩
  · rintro ⟨hx, u, ⟨hu1, hu2⟩, hu⟩
    exact ⟨hx, u, ⟨le_trans hap hu1, hu2⟩, hu⟩

sa_check_shadow_free sh_cu_1 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_cu_2 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_cu_3 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]

theorem fwd_cu_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p) ∨ x ∈ cumulative P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ cumulative P (Set.Icc a b)} =
        {x | x ∈ cumulative P (Set.Icc a p)} ∪ {x | x ∈ cumulative P (Set.Icc p b)} := by
  intro τ T M _ P a p b hap hpb
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact hT hap hpb

sa_check_fwd fwd_cu_1 cumulative_union sh_cu_1
  forbid [cumulative_inter_eq_point, cumulative_monotone, sh_cu_2, sh_cu_3]

theorem fwd_cu_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p) ∨ x ∈ cumulative P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p₁ p₂ b : τ), a ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ b → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p₁) ∨ x ∈ cumulative P (Set.Icc p₁ p₂) ∨
          x ∈ cumulative P (Set.Icc p₂ b) := by
  intro τ T M _ P a p₁ p₂ b h₁ h₂ h₃ x
  rw [hT (le_trans h₁ h₂) h₃, hT h₁ h₂, or_assoc]

sa_check_fwd fwd_cu_2 cumulative_union sh_cu_2
  forbid [cumulative_inter_eq_point, cumulative_monotone, sh_cu_1, sh_cu_3]

theorem fwd_cu_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p) ∨ x ∈ cumulative P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M),
      (x ∈ cumulative P (Set.Icc a p) → x ∈ cumulative P (Set.Icc a b)) ∧
        (x ∈ cumulative P (Set.Icc p b) → x ∈ cumulative P (Set.Icc a b)) := by
  intro τ T M _ P a p b hap hpb x
  exact ⟨fun h => (hT hap hpb).mpr (Or.inl h), fun h => (hT hap hpb).mpr (Or.inr h)⟩

sa_check_fwd fwd_cu_3 cumulative_union sh_cu_3
  forbid [cumulative_inter_eq_point, cumulative_monotone, sh_cu_1, sh_cu_2]

theorem bwd_cu
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ cumulative P (Set.Icc a b)} =
        {x | x ∈ cumulative P (Set.Icc a p)} ∪ {x | x ∈ cumulative P (Set.Icc p b)})
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p₁ p₂ b : τ), a ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ b → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p₁) ∨ x ∈ cumulative P (Set.Icc p₁ p₂) ∨
          x ∈ cumulative P (Set.Icc p₂ b))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M),
      (x ∈ cumulative P (Set.Icc a p) → x ∈ cumulative P (Set.Icc a b)) ∧
        (x ∈ cumulative P (Set.Icc p b) → x ∈ cumulative P (Set.Icc a b))) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a b) ↔
        x ∈ cumulative P (Set.Icc a p) ∨ x ∈ cumulative P (Set.Icc p b) := by
  intro τ T M _ P a p b hap hpb x
  have _ := @h₂
  have _ := @h₃
  have := Set.ext_iff.mp (h₁ P a p b hap hpb) x
  simpa only [Set.mem_setOf_eq, Set.mem_union] using this

sa_check_bwd bwd_cu cumulative_union [sh_cu_1, sh_cu_2, sh_cu_3]
  forbid [cumulative_inter_eq_point, cumulative_monotone]

/-! ## Shadows for `cumulative_inter_eq_point` -/

/-- NL: "C[a,p] ∩ C[p,b] = C[p,p]" — as an equality of sets of atoms. -/
theorem sh_ci_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) :
    {x | x ∈ cumulative P (Set.Icc a p)} ∩ {x | x ∈ cumulative P (Set.Icc p b)} =
      {x | x ∈ cumulative P (Set.Icc p p)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_cumulative]
  constructor
  · rintro ⟨⟨hx, u, ⟨hu1, hu2⟩, hu⟩, ⟨-, w, ⟨hw1, hw2⟩, hw⟩⟩
    exact ⟨hx, p, ⟨le_refl _, le_refl _⟩, (support_ordConnected x.support).out hu hw ⟨hu2, hw1⟩⟩
  · rintro ⟨hx, u, ⟨hu1, hu2⟩, hu⟩
    have : u = p := le_antisymm hu2 hu1
    subst this
    exact ⟨⟨hx, u, ⟨hap, le_refl _⟩, hu⟩, ⟨hx, u, ⟨le_refl _, hpb⟩, hu⟩⟩

/-- NL facet (the convexity content): an atom in force somewhere before `p` and
somewhere after `p` is in force *at* `p`. -/
theorem sh_ci_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (_hap : a ≤ p) (_hpb : p ≤ b) (x : Atom τ T M)
    (h₁ : x ∈ cumulative P (Set.Icc a p)) (h₂ : x ∈ cumulative P (Set.Icc p b)) :
    x ∈ active P p := by
  rw [mem_cumulative] at h₁ h₂
  obtain ⟨hx, u, ⟨-, hu2⟩, hu⟩ := h₁
  obtain ⟨-, w, ⟨hw1, -⟩, hw⟩ := h₂
  exact mem_active.mpr ⟨hx, (support_ordConnected x.support).out hu hw ⟨hu2, hw1⟩⟩

/-- NL facet (converse): an atom in force at `p` is in force somewhere in
`[a,p]` and somewhere in `[p,b]`. -/
theorem sh_ci_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a p b : τ) (hap : a ≤ p) (hpb : p ≤ b) (x : Atom τ T M) (h : x ∈ active P p) :
    x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) := by
  obtain ⟨hx, hp⟩ := mem_active.mp h
  exact ⟨mem_cumulative.mpr ⟨hx, p, ⟨hap, le_refl _⟩, hp⟩,
    mem_cumulative.mpr ⟨hx, p, ⟨le_refl _, hpb⟩, hp⟩⟩

sa_check_shadow_free sh_ci_1 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_ci_2 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_ci_3 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]

theorem fwd_ci_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) ↔
        x ∈ cumulative P (Set.Icc p p)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ cumulative P (Set.Icc a p)} ∩ {x | x ∈ cumulative P (Set.Icc p b)} =
        {x | x ∈ cumulative P (Set.Icc p p)} := by
  intro τ T M _ P a p b hap hpb
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact hT hap hpb

sa_check_fwd fwd_ci_1 cumulative_inter_eq_point sh_ci_1
  forbid [cumulative_union, cumulative_monotone, sh_ci_2, sh_ci_3]

theorem fwd_ci_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) ↔
        x ∈ cumulative P (Set.Icc p p)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a p) → x ∈ cumulative P (Set.Icc p b) → x ∈ active P p := by
  intro τ T M _ P a p b hap hpb x h₁ h₂
  exact cumulative_eq_active_of_point.mp ((hT hap hpb).mp ⟨h₁, h₂⟩)

sa_check_fwd fwd_ci_2 cumulative_inter_eq_point sh_ci_2
  forbid [cumulative_union, cumulative_monotone, sh_ci_1, sh_ci_3]

theorem fwd_ci_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) ↔
        x ∈ cumulative P (Set.Icc p p)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M), x ∈ active P p →
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) := by
  intro τ T M _ P a p b hap hpb x h
  exact (hT hap hpb).mpr (cumulative_eq_active_of_point.mpr h)

sa_check_fwd fwd_ci_3 cumulative_inter_eq_point sh_ci_3
  forbid [cumulative_union, cumulative_monotone, sh_ci_1, sh_ci_2]

theorem bwd_ci
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b →
      {x | x ∈ cumulative P (Set.Icc a p)} ∩ {x | x ∈ cumulative P (Set.Icc p b)} =
        {x | x ∈ cumulative P (Set.Icc p p)})
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a p) → x ∈ cumulative P (Set.Icc p b) → x ∈ active P p)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a p b : τ), a ≤ p → p ≤ b → ∀ (x : Atom τ T M), x ∈ active P p →
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {a p b : τ}, a ≤ p → p ≤ b → ∀ {x : Atom τ T M},
      x ∈ cumulative P (Set.Icc a p) ∧ x ∈ cumulative P (Set.Icc p b) ↔
        x ∈ cumulative P (Set.Icc p p) := by
  intro τ T M _ P a p b hap hpb x
  have _ := @h₁
  rw [cumulative_eq_active_of_point]
  exact ⟨fun h => h₂ P a p b hap hpb x h.1 h.2, h₃ P a p b hap hpb x⟩

sa_check_bwd bwd_ci cumulative_inter_eq_point [sh_ci_1, sh_ci_2, sh_ci_3]
  forbid [cumulative_union, cumulative_monotone]

/-! ## Shadows for `cumulative_monotone` -/

/-- NL: "(cosheaf)" — extension: the atoms in force somewhere in a smaller
interval are among those in force somewhere in a larger one. -/
theorem sh_cm_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (I J : Set τ) (h : I ⊆ J) : cumulative P I ⊆ cumulative P J := by
  intro x hx
  rw [mem_cumulative] at *
  exact ⟨hx.1, hx.2.mono (Set.inter_subset_inter_left _ h)⟩

/-- NL facet: for closed intervals, enlarging the interval keeps every atom. -/
theorem sh_cm_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a b a' b' : τ) (ha : a' ≤ a) (hb : b ≤ b') (x : Atom τ T M)
    (hx : x ∈ cumulative P (Set.Icc a b)) : x ∈ cumulative P (Set.Icc a' b') :=
  sh_cm_1 P _ _ (Set.Icc_subset_Icc ha hb) hx

/-- NL facet: extension is even a sublist (order of atoms preserved). -/
theorem sh_cm_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (I J : Set τ) (h : I ⊆ J) : (cumulative P I).Sublist (cumulative P J) := by
  have : cumulative P I =
      (cumulative P J).filter (fun x => decide (I ∩ x.support.memSet).Nonempty) := by
    simp only [cumulative, List.filter_filter]
    apply List.filter_congr
    intro x _
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun hI => ⟨hI, hI.mono (Set.inter_subset_inter_left _ h)⟩, fun hh => hh.1⟩
  rw [this]
  exact List.filter_sublist

sa_check_shadow_free sh_cm_1 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_cm_2 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]
sa_check_shadow_free sh_cm_3 [cumulative_union, cumulative_inter_eq_point, cumulative_monotone]

theorem fwd_cm_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ cumulative P I → x ∈ cumulative P J) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → cumulative P I ⊆ cumulative P J := by
  intro τ T M _ P I J h x hx
  exact hT h hx

sa_check_fwd fwd_cm_1 cumulative_monotone sh_cm_1
  forbid [cumulative_union, cumulative_inter_eq_point, sh_cm_2, sh_cm_3]

theorem fwd_cm_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ cumulative P I → x ∈ cumulative P J) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a b a' b' : τ), a' ≤ a → b ≤ b' → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a b) → x ∈ cumulative P (Set.Icc a' b') := by
  intro τ T M _ P a b a' b' ha hb x hx
  exact hT (Set.Icc_subset_Icc ha hb) hx

sa_check_fwd fwd_cm_2 cumulative_monotone sh_cm_2
  forbid [cumulative_union, cumulative_inter_eq_point, sh_cm_1, sh_cm_3]

theorem fwd_cm_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ cumulative P I → x ∈ cumulative P J) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → (cumulative P I).Sublist (cumulative P J) := by
  intro τ T M _ P I J h
  have key : ∀ x ∈ P, (I ∩ x.support.memSet).Nonempty → (J ∩ x.support.memSet).Nonempty := by
    intro x hx hI
    exact (mem_cumulative.mp (hT h (mem_cumulative.mpr ⟨hx, hI⟩))).2
  have : cumulative P I =
      (cumulative P J).filter (fun x => decide (I ∩ x.support.memSet).Nonempty) := by
    simp only [cumulative, List.filter_filter]
    apply List.filter_congr
    intro x hx
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun hI => ⟨hI, key x hx hI⟩, fun hh => hh.1⟩
  rw [this]
  exact List.filter_sublist

sa_check_fwd fwd_cm_3 cumulative_monotone sh_cm_3
  forbid [cumulative_union, cumulative_inter_eq_point, sh_cm_1, sh_cm_2]

theorem bwd_cm
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → cumulative P I ⊆ cumulative P J)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a b a' b' : τ), a' ≤ a → b ≤ b' → ∀ (x : Atom τ T M),
      x ∈ cumulative P (Set.Icc a b) → x ∈ cumulative P (Set.Icc a' b'))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (I J : Set τ), I ⊆ J → (cumulative P I).Sublist (cumulative P J)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M}
      {I J : Set τ}, I ⊆ J → ∀ {x : Atom τ T M}, x ∈ cumulative P I → x ∈ cumulative P J := by
  intro τ T M _ P I J h x hx
  have _ := @h₂
  have _ := @h₃
  exact h₁ P I J h hx

sa_check_bwd bwd_cm cumulative_monotone [sh_cm_1, sh_cm_2, sh_cm_3]
  forbid [cumulative_union, cumulative_inter_eq_point]

end CategoricalInterventionsProofs.SAPass.C11
