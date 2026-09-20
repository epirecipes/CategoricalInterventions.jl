import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Epoch

/-!
# SA-Pass claim 9

NL claim: **"Adding atoms only refines the epochs."**
Target: `epochs_refine`.

Reading note: the naive reading "every epoch of `P ++ Q` lies inside an epoch
of `P`" is *false* (adding a span far from `P` creates an epoch in the gap
between `P`'s spans that meets no epoch of `P`), so it cannot be a shadow.
"Refines" is read as a partition refinement: each new epoch is contained in
each old epoch it meets, equivalently no old boundary lies strictly inside a
new epoch.  The shadows pin down this reading and the corrected naive reading
("a new epoch containing a time covered by `P` lies inside an old epoch").
-/

namespace CategoricalInterventionsProofs.SAPass.C09

open CategoricalInterventionsProofs

universe u v w

/-- NL: "refines" — boundary form: no boundary of `P` lies strictly inside an
epoch of `P ++ Q`. -/
theorem sh_ref_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
    (e' : Span τ) (b : τ) (he' : e' ∈ epochs (P ++ Q)) (hb : b ∈ boundaries P) :
    ¬ (e'.lo < b ∧ b < e'.hi) :=
  (mem_epochs_iff.mp he').2.2 b (boundaries_append_left hb)

/-- NL: "refines" — partition form: each epoch of `P ++ Q` is contained in or
disjoint from each epoch of `P`. -/
theorem sh_ref_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
    (e' e : Span τ) (he' : e' ∈ epochs (P ++ Q)) (he : e ∈ epochs P) :
    e'.memSet ⊆ e.memSet ∨ e'.Disjoint e := by
  by_cases hov : e'.overlaps e
  · left
    have hel := (mem_epochs_iff.mp he).1
    have heh := (mem_epochs_iff.mp he).2.1
    have hlo : e.lo ≤ e'.lo := by
      by_contra hc
      rw [not_le] at hc
      exact sh_ref_3 P Q e' e.lo he' hel ⟨hc, hov.2⟩
    have hhi : e'.hi ≤ e.hi := by
      by_contra hc
      rw [not_le] at hc
      exact sh_ref_3 P Q e' e.hi he' heh ⟨hov.1, hc⟩
    exact Set.Ico_subset_Ico hlo hhi
  · exact Or.inr hov

/-- NL (corrected naive reading): a new epoch that contains a time covered by a
span of `P` lies inside some old epoch. -/
theorem sh_ref_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
    (e' : Span τ) (t : τ) (he' : e' ∈ epochs (P ++ Q)) (ht : InSpanUnion P t) (hte : e'.mem t) :
    ∃ e ∈ epochs P, e'.memSet ⊆ e.memSet := by
  obtain ⟨e, ⟨he, hte'⟩, -⟩ := epoch_cover ht
  refine ⟨e, he, ?_⟩
  rcases sh_ref_1 P Q e' e he' he with h | h
  · exact h
  · exact absurd (overlaps_iff_exists_mem.mpr ⟨t, hte, hte'⟩) h

sa_check_shadow_free sh_ref_1 [epochs_refine]
sa_check_shadow_free sh_ref_2 [epochs_refine]
sa_check_shadow_free sh_ref_3 [epochs_refine]

theorem fwd_ref_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P Q : Program τ T M}
      {e' : Span τ}, e' ∈ epochs (P ++ Q) → ∀ {e : Span τ}, e ∈ epochs P → e'.overlaps e →
      e'.memSet ⊆ e.memSet) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' e : Span τ), e' ∈ epochs (P ++ Q) → e ∈ epochs P →
      e'.memSet ⊆ e.memSet ∨ e'.Disjoint e := by
  intro τ T M _ P Q e' e he' he
  by_cases hov : e'.overlaps e
  · exact Or.inl (hT he' he hov)
  · exact Or.inr hov

sa_check_fwd fwd_ref_1 epochs_refine sh_ref_1 forbid [epochs_refine', sh_ref_2, sh_ref_3]

theorem fwd_ref_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P Q : Program τ T M}
      {e' : Span τ}, e' ∈ epochs (P ++ Q) → ∀ {e : Span τ}, e ∈ epochs P → e'.overlaps e →
      e'.memSet ⊆ e.memSet) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' : Span τ) (t : τ), e' ∈ epochs (P ++ Q) → InSpanUnion P t → e'.mem t →
      ∃ e ∈ epochs P, e'.memSet ⊆ e.memSet := by
  intro τ T M _ P Q e' t he' ht hte
  obtain ⟨e, ⟨he, hte'⟩, -⟩ := epoch_cover ht
  exact ⟨e, he, hT he' he (overlaps_iff_exists_mem.mpr ⟨t, hte, hte'⟩)⟩

sa_check_fwd fwd_ref_2 epochs_refine sh_ref_2 forbid [epochs_refine', sh_ref_1, sh_ref_3]

theorem fwd_ref_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P Q : Program τ T M}
      {e' : Span τ}, e' ∈ epochs (P ++ Q) → ∀ {e : Span τ}, e ∈ epochs P → e'.overlaps e →
      e'.memSet ⊆ e.memSet) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' : Span τ) (b : τ), e' ∈ epochs (P ++ Q) → b ∈ boundaries P →
      ¬ (e'.lo < b ∧ b < e'.hi) := by
  intro τ T M _ P Q e' b he' hb ⟨h1, h2⟩
  by_cases hA : ∃ c ∈ boundaries P, b < c
  · -- an old epoch starts at `b`; it meets `e'`, so `e' ⊆ e`, so `b ≤ e'.lo`
    obtain ⟨e, he, hlo⟩ := exists_consecutiveSpan_lo_eq (boundaries_sorted P) hb hA
    have hov : e'.overlaps e := by
      refine ⟨?_, ?_⟩
      · have h3 : b < e.hi := hlo ▸ e.lo_lt_hi
        exact lt_trans h1 h3
      · rw [hlo]; exact h2
    have hsub := hT he' he hov
    have hmem : e'.lo ∈ e.memSet := hsub (span_lo_mem e')
    have : e.lo ≤ e'.lo := (Set.mem_Ico.mp hmem).1
    rw [hlo] at this
    exact absurd this (not_le.mpr h1)
  · -- `b` is the greatest boundary; the old epoch ending at `b` meets `e'`
    push Not at hA
    obtain ⟨a, ha, s, hs, hbs⟩ := mem_boundarySet.mp (mem_boundaries.mp hb)
    have hslo : s.lo ∈ boundaries P := lo_mem_boundaries ha hs
    have hshi : s.hi ∈ boundaries P := hi_mem_boundaries ha hs
    have hlo_lt : s.lo < b := by
      rcases hbs with rfl | rfl
      · exact absurd (hA s.hi hshi) (not_le.mpr s.lo_lt_hi)
      · exact s.lo_lt_hi
    set L := (boundarySet P).filter (· < b) with hL
    have hLne : L.Nonempty := ⟨s.lo, Finset.mem_filter.mpr ⟨mem_boundaries.mp hslo, hlo_lt⟩⟩
    have hm := Finset.max'_mem L hLne
    have hmB : L.max' hLne ∈ boundaries P := mem_boundaries.mpr (Finset.mem_filter.mp hm).1
    have hm_lt : L.max' hLne < b := (Finset.mem_filter.mp hm).2
    have hmax : ∀ c ∈ boundaries P, c < b → c ≤ L.max' hLne := fun c hc hcb =>
      Finset.le_max' L c (Finset.mem_filter.mpr ⟨mem_boundaries.mp hc, hcb⟩)
    obtain ⟨e, he, hlo⟩ := exists_consecutiveSpan_lo_eq (boundaries_sorted P) hmB ⟨b, hb, hm_lt⟩
    have he_iff := mem_epochs_iff.mp he
    have hehi_le : e.hi ≤ b := by
      by_contra hc
      rw [not_le] at hc
      exact he_iff.2.2 b hb ⟨hlo ▸ hm_lt, hc⟩
    have hb_le : b ≤ e.hi := by
      by_contra hc
      rw [not_le] at hc
      have h3 := hmax e.hi he_iff.2.1 hc
      have h4 : L.max' hLne < e.hi := hlo ▸ e.lo_lt_hi
      exact absurd h4 (not_lt.mpr h3)
    have hov : e'.overlaps e := by
      refine ⟨lt_of_lt_of_le h1 hb_le, ?_⟩
      rw [hlo]
      exact lt_trans hm_lt h2
    have hsub := hT he' he hov
    have := (Set.Ico_subset_Ico_iff e'.lo_lt_hi).mp hsub
    exact absurd (le_trans this.2 hehi_le) (not_le.mpr h2)

sa_check_fwd fwd_ref_3 epochs_refine sh_ref_3 forbid [epochs_refine', sh_ref_1, sh_ref_2]

/-- Backward: the boundary form implies containment of overlapping epochs. -/
theorem bwd_ref
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' e : Span τ), e' ∈ epochs (P ++ Q) → e ∈ epochs P →
      e'.memSet ⊆ e.memSet ∨ e'.Disjoint e)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' : Span τ) (t : τ), e' ∈ epochs (P ++ Q) → InSpanUnion P t → e'.mem t →
      ∃ e ∈ epochs P, e'.memSet ⊆ e.memSet)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q : Program τ T M)
      (e' : Span τ) (b : τ), e' ∈ epochs (P ++ Q) → b ∈ boundaries P →
      ¬ (e'.lo < b ∧ b < e'.hi)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P Q : Program τ T M}
      {e' : Span τ}, e' ∈ epochs (P ++ Q) → ∀ {e : Span τ}, e ∈ epochs P → e'.overlaps e →
      e'.memSet ⊆ e.memSet := by
  intro τ T M _ P Q e' he' e he hov
  have _ := @h₁
  have _ := @h₂
  have hel := (mem_epochs_iff.mp he).1
  have heh := (mem_epochs_iff.mp he).2.1
  have hlo : e.lo ≤ e'.lo := by
    by_contra hc
    rw [not_le] at hc
    exact h₃ P Q e' e.lo he' hel ⟨hc, hov.2⟩
  have hhi : e'.hi ≤ e.hi := by
    by_contra hc
    rw [not_le] at hc
    exact h₃ P Q e' e.hi he' heh ⟨hov.1, hc⟩
  exact Set.Ico_subset_Ico hlo hhi

sa_check_bwd bwd_ref epochs_refine [sh_ref_1, sh_ref_2, sh_ref_3] forbid [epochs_refine']

end CategoricalInterventionsProofs.SAPass.C09
