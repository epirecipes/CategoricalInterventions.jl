import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Lowering

/-!
# SA-Pass claim 17

NL claim: **"Holding each parameter from one event to the next reproduces the
schedule (callback correctness)."**
Target: `lower_eq_apply`.

Scope note: the theorem is for span-only programs with a constant baseline;
the sentence mentions neither.  Both are needed with the definitions as they
stand (`lower` samples `P ▷ (fun _ => θ₀)`; holding a pulse's value past its
instant would be wrong), so the shadows carry them.
-/

namespace CategoricalInterventionsProofs.SAPass.C17

open CategoricalInterventionsProofs

universe u v w x

/-- NL: "reproduces the schedule" — at every event, the held value is the
schedule's value there. -/
theorem sh_low_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (_hP : SpanOnly P) (θ0 : T → V)
    (j : T) (e : τ) (he : e ∈ events P) :
    holdLast (lower P θ0 j) (θ0 j) e = apply P (fun _ => θ0) e j := by
  have hsorted : (lower P θ0 j).Pairwise (fun a b => a.1 < b.1) := by
    simp only [lower, List.pairwise_map]
    exact events_sorted P
  refine holdLast_eq_of_max hsorted (e := (e, apply P (fun _ => θ0) e j)) ?_ (le_refl _)
    (fun _ _ h => h) (θ0 j)
  simp only [lower, List.mem_map]
  exact ⟨e, he, rfl⟩

/-- NL: "holding … from one event to the next" — before the first event the
held value is the baseline. -/
theorem sh_low_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (_hP : SpanOnly P) (θ0 : T → V)
    (j : T) (t : τ) (h : ∀ e ∈ events P, t < e) :
    holdLast (lower P θ0 j) (θ0 j) t = θ0 j := by
  apply holdLast_eq_default
  intro e he
  simp only [lower, List.mem_map] at he
  obtain ⟨b, hb, rfl⟩ := he
  exact h b hb

/-- NL: "reproduces the schedule" — the whole held trajectory equals the whole
schedule (as functions of time).  Proved through the target: this facet *is*
the theorem's content. -/
theorem sh_low_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (hP : SpanOnly P) (θ0 : T → V)
    (j : T) : (fun t => holdLast (lower P θ0 j) (θ0 j) t) = fun t => apply P (fun _ => θ0) t j := by
  funext t
  exact lower_eq_apply hP θ0 j t

sa_check_shadow_free sh_low_1 [lower_eq_apply]
sa_check_shadow_free sh_low_2 [lower_eq_apply]
sa_check_shadow_via sh_low_3 lower_eq_apply

theorem fwd_low_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M}, SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      holdLast (lower P θ0 j) (θ0 j) t = apply P (fun _ => θ0) t j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T) (e : τ),
      e ∈ events P → holdLast (lower P θ0 j) (θ0 j) e = apply P (fun _ => θ0) e j := by
  intro τ T M V _ _ _ _ P hP θ0 j e _
  exact hT hP θ0 j e

sa_check_fwd fwd_low_1 lower_eq_apply sh_low_1 forbid [sh_low_2, sh_low_3]

theorem fwd_low_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M}, SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      holdLast (lower P θ0 j) (θ0 j) t = apply P (fun _ => θ0) t j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      (∀ e ∈ events P, t < e) → holdLast (lower P θ0 j) (θ0 j) t = θ0 j := by
  intro τ T M V _ _ _ _ P hP θ0 j t h
  rw [hT hP θ0 j t]
  have hloc : ∀ a ∈ P, ¬ a.support.mem t := by
    intro a ha hm
    obtain ⟨s, hs⟩ := hP a ha
    rw [hs] at hm
    have hlo : s.lo ∈ events P := by
      rw [mem_events, eventSet_eq_boundarySet hP]
      exact mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩
    exact absurd hm.1 (not_le.mpr (h s.lo hlo))
  exact congrFun (apply_local hloc (fun _ => θ0)) j

sa_check_fwd fwd_low_2 lower_eq_apply sh_low_2 forbid [sh_low_1, sh_low_3]

theorem fwd_low_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M}, SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      holdLast (lower P θ0 j) (θ0 j) t = apply P (fun _ => θ0) t j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T),
      (fun t => holdLast (lower P θ0 j) (θ0 j) t) = fun t => apply P (fun _ => θ0) t j := by
  intro τ T M V _ _ _ _ P hP θ0 j
  funext t
  exact hT hP θ0 j t

sa_check_fwd fwd_low_3 lower_eq_apply sh_low_3 forbid [sh_low_1, sh_low_2]

theorem bwd_low
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T) (e : τ),
      e ∈ events P → holdLast (lower P θ0 j) (θ0 j) e = apply P (fun _ => θ0) e j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      (∀ e ∈ events P, t < e) → holdLast (lower P θ0 j) (θ0 j) t = θ0 j)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M), SpanOnly P → ∀ (θ0 : T → V) (j : T),
      (fun t => holdLast (lower P θ0 j) (θ0 j) t) = fun t => apply P (fun _ => θ0) t j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M}, SpanOnly P → ∀ (θ0 : T → V) (j : T) (t : τ),
      holdLast (lower P θ0 j) (θ0 j) t = apply P (fun _ => θ0) t j := by
  intro τ T M V _ _ _ _ P hP θ0 j t
  have _ := @h₁
  have _ := @h₂
  exact congrFun (h₃ P hP θ0 j) t

sa_check_bwd bwd_low lower_eq_apply [sh_low_1, sh_low_2, sh_low_3]

end CategoricalInterventionsProofs.SAPass.C17
