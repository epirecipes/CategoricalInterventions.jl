import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Semantics

/-!
# SA-Pass claim 13

NL claim: **"The empty program does nothing; outside every support the schedule
is unchanged."**
Targets: `apply_nil`, `apply_local`.
-/

namespace CategoricalInterventionsProofs.SAPass.C13

open CategoricalInterventionsProofs

universe u v w x

/-! ## Shadows for `apply_nil` -/

/-- NL: "the empty program does nothing" — pointwise, at every time and target. -/
theorem sh_nil_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (θ : τ → T → V) (t : τ) (j : T) :
    apply ([] : Program τ T M) θ t j = θ t j := by
  simp [apply, act_one]

/-- NL facet: doing nothing twice is still doing nothing. -/
theorem sh_nil_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (θ : τ → T → V) :
    apply ([] : Program τ T M) (apply ([] : Program τ T M) θ) = θ := by
  funext t j
  rw [sh_nil_1, sh_nil_1]

sa_check_shadow_free sh_nil_1 [apply_nil, apply_local]
sa_check_shadow_free sh_nil_2 [apply_nil, apply_local]

theorem fwd_nil_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V), apply ([] : Program τ T M) θ = θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V) (t : τ) (j : T),
      apply ([] : Program τ T M) θ t j = θ t j := by
  intro τ T M V _ _ _ _ θ t j
  rw [hT]

sa_check_fwd fwd_nil_1 apply_nil sh_nil_1 forbid [apply_local, sh_nil_2]

theorem fwd_nil_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V), apply ([] : Program τ T M) θ = θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V),
      apply ([] : Program τ T M) (apply ([] : Program τ T M) θ) = θ := by
  intro τ T M V _ _ _ _ θ
  rw [hT, hT]

sa_check_fwd fwd_nil_2 apply_nil sh_nil_2 forbid [apply_local, sh_nil_1]

theorem bwd_nil
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V) (t : τ) (j : T),
      apply ([] : Program τ T M) θ t j = θ t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V),
      apply ([] : Program τ T M) (apply ([] : Program τ T M) θ) = θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (θ : τ → T → V), apply ([] : Program τ T M) θ = θ := by
  intro τ T M V _ _ _ _ θ
  have _ := @h₂
  funext t j
  exact h₁ θ t j

sa_check_bwd bwd_nil apply_nil [sh_nil_1, sh_nil_2] forbid [apply_local]

/-! ## Shadows for `apply_local` -/

/-- NL: "outside every support the schedule is unchanged" — with "outside every
support" as non-membership in the union of the supports. -/
theorem sh_loc_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ)
    (h : t ∉ ⋃ a ∈ P, a.support.memSet) (θ : τ → T → V) : apply P θ t = θ t := by
  funext j
  simp only [apply]
  rw [foldAt_eq_one_of_not_active j P t (fun a ha hm => h (Set.mem_iUnion₂.mpr ⟨a, ha, hm⟩))]
  exact act_one _

/-- NL facet: pointwise per target. -/
theorem sh_loc_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ)
    (h : ∀ a ∈ P, ¬ a.support.mem t) (θ : τ → T → V) (j : T) : apply P θ t j = θ t j := by
  simp only [apply]
  rw [foldAt_eq_one_of_not_active j P t h]
  exact act_one _

/-- NL facet: after every span has ended and every pulse has fired, the
schedule is the baseline. -/
theorem sh_loc_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ)
    (hs : ∀ a ∈ P, ∀ s : Span τ, a.support = .span s → s.hi ≤ t)
    (hi : ∀ a ∈ P, ∀ i : Instant τ, a.support = .instant i → i.time < t)
    (θ : τ → T → V) : apply P θ t = θ t := by
  funext j
  apply sh_loc_2 P t _ θ j
  intro a ha hm
  rcases hsup : a.support with s | i
  · rw [hsup] at hm
    exact absurd (lt_of_lt_of_le hm.2 (hs a ha s hsup)) (lt_irrefl t)
  · rw [hsup] at hm
    rw [Support.mem_instant] at hm
    exact absurd (hm ▸ hi a ha i hsup) (lt_irrefl t)

sa_check_shadow_free sh_loc_1 [apply_nil, apply_local]
sa_check_shadow_free sh_loc_2 [apply_nil, apply_local]
sa_check_shadow_free sh_loc_3 [apply_nil, apply_local]

theorem fwd_loc_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M} {t : τ}, (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ), t ∉ ⋃ a ∈ P, a.support.memSet →
      ∀ (θ : τ → T → V), apply P θ t = θ t := by
  intro τ T M V _ _ _ _ P t h θ
  exact hT (fun a ha hm => h (Set.mem_iUnion₂.mpr ⟨a, ha, hm⟩)) θ

sa_check_fwd fwd_loc_1 apply_local sh_loc_1 forbid [apply_nil, sh_loc_2, sh_loc_3]

theorem fwd_loc_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M} {t : τ}, (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ), (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V) (j : T), apply P θ t j = θ t j := by
  intro τ T M V _ _ _ _ P t h θ j
  rw [hT h θ]

sa_check_fwd fwd_loc_2 apply_local sh_loc_2 forbid [apply_nil, sh_loc_1, sh_loc_3]

theorem fwd_loc_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M} {t : τ}, (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ),
      (∀ a ∈ P, ∀ s : Span τ, a.support = .span s → s.hi ≤ t) →
      (∀ a ∈ P, ∀ i : Instant τ, a.support = .instant i → i.time < t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t := by
  intro τ T M V _ _ _ _ P t hs hi θ
  apply hT _ θ
  intro a ha hm
  rcases hsup : a.support with s | i
  · rw [hsup] at hm
    exact absurd (lt_of_lt_of_le hm.2 (hs a ha s hsup)) (lt_irrefl t)
  · rw [hsup] at hm
    rw [Support.mem_instant] at hm
    exact absurd (hm ▸ hi a ha i hsup) (lt_irrefl t)

sa_check_fwd fwd_loc_3 apply_local sh_loc_3 forbid [apply_nil, sh_loc_1, sh_loc_2]

theorem bwd_loc
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ), t ∉ ⋃ a ∈ P, a.support.memSet →
      ∀ (θ : τ → T → V), apply P θ t = θ t)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ), (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V) (j : T), apply P θ t j = θ t j)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P : Program τ T M) (t : τ),
      (∀ a ∈ P, ∀ s : Span τ, a.support = .span s → s.hi ≤ t) →
      (∀ a ∈ P, ∀ i : Instant τ, a.support = .instant i → i.time < t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P : Program τ T M} {t : τ}, (∀ a ∈ P, ¬ a.support.mem t) →
      ∀ (θ : τ → T → V), apply P θ t = θ t := by
  intro τ T M V _ _ _ _ P t h θ
  have _ := @h₁
  have _ := @h₃
  funext j
  exact h₂ P t h θ j

sa_check_bwd bwd_loc apply_local [sh_loc_1, sh_loc_2, sh_loc_3] forbid [apply_nil]

end CategoricalInterventionsProofs.SAPass.C13
