import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Semantics

/-!
# SA-Pass claim 16

NL claim: **"The schedule is constant on each epoch when the baseline is."**
Target: `apply_const_on_epoch`.

Scope note: as for claim 8, the statement is false for programs with instants,
so the shadows carry `SpanOnly P`.
-/

namespace CategoricalInterventionsProofs.SAPass.C16

open CategoricalInterventionsProofs

universe u v w x

/-- NL: "the schedule is constant on each epoch when the baseline is" — for a
globally constant baseline. -/
theorem sh_ce_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (hP : SpanOnly P) (e : Span τ)
    (he : e ∈ epochs P) (θ₀ : T → V) (t t' : τ) (ht : e.mem t) (ht' : e.mem t') :
    apply P (fun _ => θ₀) t = apply P (fun _ => θ₀) t' := by
  funext j
  simp only [apply, foldAt, effectsAt]
  rw [active_const_on_epoch hP he ht ht']

/-- NL facet: anchored at the epoch start — a baseline that agrees with its
value at `e.lo` throughout `e` gives a schedule that does too. -/
theorem sh_ce_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (hP : SpanOnly P) (e : Span τ)
    (he : e ∈ epochs P) (θ : τ → T → V) (hθ : ∀ t, e.mem t → θ t = θ e.lo) (t : τ)
    (ht : e.mem t) : apply P θ t = apply P θ e.lo := by
  funext j
  simp only [apply, foldAt, effectsAt]
  rw [active_const_on_epoch hP he ht (span_lo_mem e), hθ t ht]

/-- NL: "when the baseline is [constant on the epoch]" — with constancy spelled
out as "there is a value the baseline takes throughout the epoch". -/
theorem sh_ce_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (hP : SpanOnly P) (e : Span τ)
    (he : e ∈ epochs P) (θ : τ → T → V) (hθ : ∃ c : T → V, ∀ t, e.mem t → θ t = c) (t t' : τ)
    (ht : e.mem t) (ht' : e.mem t') : apply P θ t = apply P θ t' := by
  obtain ⟨c, hc⟩ := hθ
  funext j
  simp only [apply, foldAt, effectsAt]
  rw [active_const_on_epoch hP he ht ht', hc t ht, hc t' ht']

sa_check_shadow_free sh_ce_1 [apply_const_on_epoch]
sa_check_shadow_free sh_ce_2 [apply_const_on_epoch]
sa_check_shadow_free sh_ce_3 [apply_const_on_epoch]

theorem fwd_ce_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P : Program τ T M}, SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P →
      ∀ {θ : τ → T → V}, (∀ (t t' : τ), e.mem t → e.mem t' → θ t = θ t') →
      ∀ {t t' : τ}, e.mem t → e.mem t' → apply P θ t = apply P θ t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ₀ : T → V) (t t' : τ), e.mem t → e.mem t' →
      apply P (fun _ => θ₀) t = apply P (fun _ => θ₀) t' := by
  intro τ T M V _ _ _ _ P hP e he θ₀ t t' ht ht'
  exact hT hP he (fun _ _ _ _ => rfl) ht ht'

sa_check_fwd fwd_ce_1 apply_const_on_epoch sh_ce_1 forbid [active_const_on_epoch, sh_ce_2, sh_ce_3]

theorem fwd_ce_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P : Program τ T M}, SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P →
      ∀ {θ : τ → T → V}, (∀ (t t' : τ), e.mem t → e.mem t' → θ t = θ t') →
      ∀ {t t' : τ}, e.mem t → e.mem t' → apply P θ t = apply P θ t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ : τ → T → V), (∀ t, e.mem t → θ t = θ e.lo) → ∀ (t : τ), e.mem t →
      apply P θ t = apply P θ e.lo := by
  intro τ T M V _ _ _ _ P hP e he θ hθ t ht
  exact hT hP he (fun s s' hs hs' => (hθ s hs).trans (hθ s' hs').symm) ht (span_lo_mem e)

sa_check_fwd fwd_ce_2 apply_const_on_epoch sh_ce_2 forbid [active_const_on_epoch, sh_ce_1, sh_ce_3]

theorem fwd_ce_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P : Program τ T M}, SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P →
      ∀ {θ : τ → T → V}, (∀ (t t' : τ), e.mem t → e.mem t' → θ t = θ t') →
      ∀ {t t' : τ}, e.mem t → e.mem t' → apply P θ t = apply P θ t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ : τ → T → V), (∃ c : T → V, ∀ t, e.mem t → θ t = c) → ∀ (t t' : τ),
      e.mem t → e.mem t' → apply P θ t = apply P θ t' := by
  intro τ T M V _ _ _ _ P hP e he θ ⟨c, hc⟩ t t' ht ht'
  exact hT hP he (fun s s' hs hs' => (hc s hs).trans (hc s' hs').symm) ht ht'

sa_check_fwd fwd_ce_3 apply_const_on_epoch sh_ce_3 forbid [active_const_on_epoch, sh_ce_1, sh_ce_2]

theorem bwd_ce
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ₀ : T → V) (t t' : τ), e.mem t → e.mem t' →
      apply P (fun _ => θ₀) t = apply P (fun _ => θ₀) t')
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ : τ → T → V), (∀ t, e.mem t → θ t = θ e.lo) → ∀ (t : τ), e.mem t →
      apply P θ t = apply P θ e.lo)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M), SpanOnly P → ∀ (e : Span τ), e ∈ epochs P →
      ∀ (θ : τ → T → V), (∃ c : T → V, ∀ t, e.mem t → θ t = c) → ∀ (t t' : τ),
      e.mem t → e.mem t' → apply P θ t = apply P θ t') :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P : Program τ T M}, SpanOnly P → ∀ {e : Span τ}, e ∈ epochs P →
      ∀ {θ : τ → T → V}, (∀ (t t' : τ), e.mem t → e.mem t' → θ t = θ t') →
      ∀ {t t' : τ}, e.mem t → e.mem t' → apply P θ t = apply P θ t' := by
  intro τ T M V _ _ _ _ P hP e he θ hθ t t' ht ht'
  have _ := @h₁
  have _ := @h₂
  exact h₃ P hP e he θ ⟨θ t, fun s hs => hθ s t hs ht⟩ t t' ht ht'

sa_check_bwd bwd_ce apply_const_on_epoch [sh_ce_1, sh_ce_2, sh_ce_3] forbid [active_const_on_epoch]

end CategoricalInterventionsProofs.SAPass.C16
