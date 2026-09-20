import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Epoch

/-!
# SA-Pass claim 8

NL claim: **"Every time inside a span lies in exactly one epoch, and the active
set is constant on an epoch."**
Targets: `epoch_cover`, `active_const_on_epoch`.

Scope note: "the active set is constant on an epoch" is false for programs with
instants (a pulse inside an epoch changes the active set at its time), so the
shadows carry the `SpanOnly P` hypothesis the theorem carries; the sentence
should say "for span-only programs".
-/

namespace CategoricalInterventionsProofs.SAPass.C08

open CategoricalInterventionsProofs

universe u v w

/-! ## Shadows for `epoch_cover` -/

/-- NL: "every time inside a span lies in (at least) one epoch" — existence. -/
theorem sh_ec_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (t : τ) (h : InSpanUnion P t) : ∃ e ∈ epochs P, e.mem t := by
  obtain ⟨a, ha, s, hs, hlo, hhi⟩ := h
  have hlo_mem : s.lo ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩
  have hhi_mem : s.hi ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inr rfl⟩
  set L := (boundarySet P).filter (· ≤ t) with hL
  set U := (boundarySet P).filter (t < ·) with hU
  have hLne : L.Nonempty := ⟨s.lo, Finset.mem_filter.mpr ⟨hlo_mem, hlo⟩⟩
  have hUne : U.Nonempty := ⟨s.hi, Finset.mem_filter.mpr ⟨hhi_mem, hhi⟩⟩
  have hlo'_mem := Finset.max'_mem L hLne
  have hhi'_mem := Finset.min'_mem U hUne
  have hlo'_le : L.max' hLne ≤ t := (Finset.mem_filter.mp hlo'_mem).2
  have hlt_hi' : t < U.min' hUne := (Finset.mem_filter.mp hhi'_mem).2
  refine ⟨⟨L.max' hLne, U.min' hUne, lt_of_le_of_lt hlo'_le hlt_hi'⟩, ?_, ⟨hlo'_le, hlt_hi'⟩⟩
  rw [mem_epochs_iff]
  refine ⟨mem_boundaries.mpr (Finset.mem_filter.mp hlo'_mem).1,
    mem_boundaries.mpr (Finset.mem_filter.mp hhi'_mem).1, ?_⟩
  intro b hb ⟨h1, h2⟩
  rcases le_or_gt b t with hbt | hbt
  · exact absurd (Finset.le_max' L b (Finset.mem_filter.mpr ⟨mem_boundaries.mp hb, hbt⟩))
      (not_le.mpr h1)
  · exact absurd (Finset.min'_le U b (Finset.mem_filter.mpr ⟨mem_boundaries.mp hb, hbt⟩))
      (not_le.mpr h2)

/-- NL: "… lies in *exactly* one epoch" — uniqueness, for a time inside a span. -/
theorem sh_ec_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (t : τ) (_h : InSpanUnion P t) (e₁ e₂ : Span τ) (he₁ : e₁ ∈ epochs P) (he₂ : e₂ ∈ epochs P)
    (ht₁ : e₁.mem t) (ht₂ : e₂.mem t) : e₁ = e₂ := by
  by_contra hne
  have hsymm : Symmetric (Span.Disjoint (τ := τ)) := fun s s' h hov => h (overlaps_symm hov)
  exact ((epochs_pairwise_disjoint P).forall hsymm he₁ he₂ hne).not_mem ht₁ ht₂

/-- NL: "inside a span" spelled out — a time in the span of some atom of `P`
lies in an epoch of `P`. -/
theorem sh_ec_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (a : Atom τ T M) (ha : a ∈ P) (s : Span τ) (hs : a.support = .span s) (t : τ)
    (ht : s.mem t) : ∃ e ∈ epochs P, e.mem t :=
  sh_ec_1 P t ⟨a, ha, s, hs, ht⟩

sa_check_shadow_free sh_ec_1 [epoch_cover, active_const_on_epoch]
sa_check_shadow_free sh_ec_2 [epoch_cover, active_const_on_epoch]
sa_check_shadow_free sh_ec_3 [epoch_cover, active_const_on_epoch]

theorem fwd_ec_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M} {t : τ},
      InSpanUnion P t → ∃! e : Span τ, e ∈ epochs P ∧ e.mem t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (t : τ),
      InSpanUnion P t → ∃ e ∈ epochs P, e.mem t := by
  intro τ T M _ P t h
  obtain ⟨e, ⟨he, ht⟩, -⟩ := hT h
  exact ⟨e, he, ht⟩

sa_check_fwd fwd_ec_1 epoch_cover sh_ec_1 forbid [active_const_on_epoch, sh_ec_2, sh_ec_3]

theorem fwd_ec_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M} {t : τ},
      InSpanUnion P t → ∃! e : Span τ, e ∈ epochs P ∧ e.mem t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (t : τ),
      InSpanUnion P t → ∀ (e₁ e₂ : Span τ), e₁ ∈ epochs P → e₂ ∈ epochs P →
      e₁.mem t → e₂.mem t → e₁ = e₂ := by
  intro τ T M _ P t h e₁ e₂ he₁ he₂ ht₁ ht₂
  exact (hT h).unique ⟨he₁, ht₁⟩ ⟨he₂, ht₂⟩

sa_check_fwd fwd_ec_2 epoch_cover sh_ec_2 forbid [active_const_on_epoch, sh_ec_1, sh_ec_3]

theorem fwd_ec_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M} {t : τ},
      InSpanUnion P t → ∃! e : Span τ, e ∈ epochs P ∧ e.mem t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a : Atom τ T M), a ∈ P → ∀ (s : Span τ), a.support = .span s → ∀ (t : τ),
      s.mem t → ∃ e ∈ epochs P, e.mem t := by
  intro τ T M _ P a ha s hs t ht
  obtain ⟨e, ⟨he, ht'⟩, -⟩ := hT ⟨a, ha, s, hs, ht⟩
  exact ⟨e, he, ht'⟩

sa_check_fwd fwd_ec_3 epoch_cover sh_ec_3 forbid [active_const_on_epoch, sh_ec_1, sh_ec_2]

theorem bwd_ec
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (t : τ),
      InSpanUnion P t → ∃ e ∈ epochs P, e.mem t)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (t : τ),
      InSpanUnion P t → ∀ (e₁ e₂ : Span τ), e₁ ∈ epochs P → e₂ ∈ epochs P →
      e₁.mem t → e₂.mem t → e₁ = e₂)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
      (a : Atom τ T M), a ∈ P → ∀ (s : Span τ), a.support = .span s → ∀ (t : τ),
      s.mem t → ∃ e ∈ epochs P, e.mem t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M} {t : τ},
      InSpanUnion P t → ∃! e : Span τ, e ∈ epochs P ∧ e.mem t := by
  intro τ T M _ P t h
  have _ := @h₃
  obtain ⟨e, he, ht⟩ := h₁ P t h
  exact ⟨e, ⟨he, ht⟩, fun e' ⟨he', ht'⟩ => h₂ P t h e' e he' he ht' ht⟩

sa_check_bwd bwd_ec epoch_cover [sh_ec_1, sh_ec_2, sh_ec_3] forbid [active_const_on_epoch]

/-! ## Shadows for `active_const_on_epoch` -/

/-- NL: "the active set is constant on an epoch" — atom by atom: within one
epoch, each atom is either in force at both times or at neither. -/
theorem sh_ac_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (hP : SpanOnly P) (e : Span τ) (he : e ∈ epochs P) (t t' : τ) (ht : e.mem t)
    (ht' : e.mem t') : ∀ a ∈ P, (a.support.mem t ↔ a.support.mem t') := by
  intro a ha
  obtain ⟨s, hs⟩ := hP a ha
  rw [hs, Support.mem_span, Support.mem_span,
    span_mem_iff_of_epoch he (lo_mem_boundaries ha hs) (hi_mem_boundaries ha hs) ht,
    span_mem_iff_of_epoch he (lo_mem_boundaries ha hs) (hi_mem_boundaries ha hs) ht']

/-- NL facet: the active set anywhere in an epoch is the active set at the
epoch's start. -/
theorem sh_ac_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M)
    (hP : SpanOnly P) (e : Span τ) (he : e ∈ epochs P) (t : τ) (ht : e.mem t) :
    active P t = active P e.lo := by
  unfold active
  apply List.filter_congr
  intro a ha
  rw [decide_eq_decide]
  exact sh_ac_1 P hP e he t e.lo ht (span_lo_mem e) a ha

/-- NL facet: consequently every fold is constant on an epoch. -/
theorem sh_ac_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (P : Program τ T M) (hP : SpanOnly P) (e : Span τ) (he : e ∈ epochs P) (t t' : τ)
    (ht : e.mem t) (ht' : e.mem t') : ∀ j, foldAt j P t = foldAt j P t' := by
  intro j
  simp only [foldAt, effectsAt, sh_ac_3 P hP e he t ht, sh_ac_3 P hP e he t' ht']

sa_check_shadow_free sh_ac_1 [epoch_cover, active_const_on_epoch]
sa_check_shadow_free sh_ac_2 [epoch_cover, active_const_on_epoch]
sa_check_shadow_free sh_ac_3 [epoch_cover, active_const_on_epoch]

theorem fwd_ac_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M},
      SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P → ∀ {t t' : τ}, e.mem t → e.mem t' →
      active P t = active P t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t t' : τ), e.mem t → e.mem t' →
      ∀ a ∈ P, (a.support.mem t ↔ a.support.mem t') := by
  intro τ T M _ P hP e he t t' ht ht' a ha
  have hact := hT hP he ht ht'
  constructor
  · intro hm
    have : a ∈ active P t' := hact ▸ mem_active.mpr ⟨ha, hm⟩
    exact (mem_active.mp this).2
  · intro hm
    have : a ∈ active P t := hact ▸ mem_active.mpr ⟨ha, hm⟩
    exact (mem_active.mp this).2

sa_check_fwd fwd_ac_1 active_const_on_epoch sh_ac_1
  forbid [epoch_cover, span_mem_iff_of_epoch, sh_ac_2, sh_ac_3]

theorem fwd_ac_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M},
      SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P → ∀ {t t' : τ}, e.mem t → e.mem t' →
      active P t = active P t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t t' : τ),
      e.mem t → e.mem t' → ∀ j, foldAt j P t = foldAt j P t' := by
  intro τ T M _ _ _ P hP e he t t' ht ht' j
  simp only [foldAt, effectsAt, hT hP he ht ht']

sa_check_fwd fwd_ac_2 active_const_on_epoch sh_ac_2
  forbid [epoch_cover, span_mem_iff_of_epoch, sh_ac_1, sh_ac_3]

theorem fwd_ac_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M},
      SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P → ∀ {t t' : τ}, e.mem t → e.mem t' →
      active P t = active P t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t : τ), e.mem t →
      active P t = active P e.lo := by
  intro τ T M _ P hP e he t ht
  exact hT hP he ht (span_lo_mem e)

sa_check_fwd fwd_ac_3 active_const_on_epoch sh_ac_3
  forbid [epoch_cover, span_mem_iff_of_epoch, sh_ac_1, sh_ac_2]

theorem bwd_ac
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t t' : τ), e.mem t → e.mem t' →
      ∀ a ∈ P, (a.support.mem t ↔ a.support.mem t'))
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t t' : τ),
      e.mem t → e.mem t' → ∀ j, foldAt j P t = foldAt j P t')
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      SpanOnly P → ∀ (e : Span τ), e ∈ epochs P → ∀ (t : τ), e.mem t →
      active P t = active P e.lo) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] {P : Program τ T M},
      SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P → ∀ {t t' : τ}, e.mem t → e.mem t' →
      active P t = active P t' := by
  intro τ T M _ P hP e he t t' ht ht'
  have _ := @h₂
  have _ := @h₃
  unfold active
  apply List.filter_congr
  intro a ha
  rw [decide_eq_decide]
  exact h₁ P hP e he t t' ht ht' a ha

sa_check_bwd bwd_ac active_const_on_epoch [sh_ac_1, sh_ac_2, sh_ac_3]
  forbid [epoch_cover, span_mem_iff_of_epoch]

end CategoricalInterventionsProofs.SAPass.C08
