import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.Common
import CategoricalInterventionsProofs.Semantics

/-!
# SA-Pass claim 14

NL claim: **"Applying P then Q equals applying P ⊕ Q (acting algebras; under
Affine when Q is purely relative)."**
Targets: `apply_append`, `apply_append_affine`.

Scope note: the sentence does not mention conflict-freeness, but the claim is
false without it (an undefined fold acts trivially while the sequential
application does not), so every shadow carries `ConflictFree (P ++ Q)`.  The
sentence should say "for a conflict-free composite".
-/

namespace CategoricalInterventionsProofs.SAPass.C14

open CategoricalInterventionsProofs

universe u v w x

/-! ## Shadows for `apply_append` -/

/-- NL: "applying P then Q equals applying P ⊕ Q" — pointwise, with the
composite written with `⊕ᵢ`. -/
theorem sh_app_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M) (h : ConflictFree (P ⊕ᵢ Q))
    (θ : τ → T → V) (t : τ) (j : T) : apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j := by
  have h1 : (foldAt j (P ++ Q) t).isSome := h t j
  rw [foldAt_append] at h1
  change actOpt (foldAt j (P ++ Q) t) (θ t j) = _
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at h1
    · rw [hP, hQ] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      exact act_mul' (V := V) (θ t j) hc

/-- NL facet: the composite may equally be applied as "Q then P" (the order of
sequential application is irrelevant for a conflict-free composite). -/
theorem sh_app_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M) (h : ConflictFree (P ++ Q))
    (θ : τ → T → V) : apply (P ++ Q) θ = apply P (apply Q θ) := by
  funext t j
  have h1 := h t j
  rw [foldAt_append] at h1
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at h1
    · rw [hP, hQ] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      exact act_mul (V := V) _ _ _ (θ t j) hc

/-- NL facet (iterated): three programs applied in sequence. -/
theorem sh_app_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [PCMAction M V] (P Q R : Program τ T M)
    (h : ConflictFree ((P ⊕ᵢ Q) ⊕ᵢ R)) (θ : τ → T → V) :
    apply ((P ⊕ᵢ Q) ⊕ᵢ R) θ = apply R (apply Q (apply P θ)) := by
  have hPQ : ConflictFree (P ⊕ᵢ Q) := conflictFree_of_append_left (P := P ⊕ᵢ Q) (Q := R) h
  have e1 : apply (P ⊕ᵢ Q) θ = apply Q (apply P θ) :=
    funext fun t => funext fun j => sh_app_1 P Q hPQ θ t j
  funext t j
  rw [sh_app_1 (P ⊕ᵢ Q) R h θ t j, e1]

sa_check_shadow_free sh_app_1 [apply_append, apply_append_affine, apply_append']
sa_check_shadow_free sh_app_2 [apply_append, apply_append_affine, apply_append']
sa_check_shadow_free sh_app_3 [apply_append, apply_append_affine, apply_append']

theorem fwd_app_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P Q : Program τ T M}, ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q : Program τ T M), ConflictFree (P ⊕ᵢ Q) →
      ∀ (θ : τ → T → V) (t : τ) (j : T), apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j := by
  intro τ T M V _ _ _ _ P Q h θ t j
  exact congrFun (congrFun (hT h θ) t) j

sa_check_fwd fwd_app_1 apply_append sh_app_1 forbid [apply_append_affine, apply_append', sh_app_2, sh_app_3]

theorem fwd_app_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P Q : Program τ T M}, ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q : Program τ T M), ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply P (apply Q θ) := by
  intro τ T M V _ _ _ _ P Q h θ
  have h' : ConflictFree (Q ++ P) := fun t j => by
    rw [foldAt_perm List.perm_append_comm]; exact h t j
  rw [apply_comm, hT h' θ]

sa_check_fwd fwd_app_2 apply_append sh_app_2 forbid [apply_append_affine, apply_append', sh_app_1, sh_app_3]

theorem fwd_app_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P Q : Program τ T M}, ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q R : Program τ T M), ConflictFree ((P ⊕ᵢ Q) ⊕ᵢ R) →
      ∀ (θ : τ → T → V), apply ((P ⊕ᵢ Q) ⊕ᵢ R) θ = apply R (apply Q (apply P θ)) := by
  intro τ T M V _ _ _ _ P Q R h θ
  have h' : ConflictFree ((P ++ Q) ++ R) := h
  have hPQ : ConflictFree (P ++ Q) := conflictFree_of_append_left h'
  change apply ((P ++ Q) ++ R) θ = _
  rw [hT h' θ, hT hPQ θ]

sa_check_fwd fwd_app_3 apply_append sh_app_3 forbid [apply_append_affine, apply_append', sh_app_1, sh_app_2]

theorem bwd_app
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q : Program τ T M), ConflictFree (P ⊕ᵢ Q) →
      ∀ (θ : τ → T → V) (t : τ) (j : T), apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q : Program τ T M), ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply P (apply Q θ))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] (P Q R : Program τ T M), ConflictFree ((P ⊕ᵢ Q) ⊕ᵢ R) →
      ∀ (θ : τ → T → V), apply ((P ⊕ᵢ Q) ⊕ᵢ R) θ = apply R (apply Q (apply P θ))) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [PCMAction M V] {P Q : Program τ T M}, ConflictFree (P ++ Q) →
      ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ) := by
  intro τ T M V _ _ _ _ P Q h θ
  have _ := @h₂
  have _ := @h₃
  funext t j
  exact h₁ P Q h θ t j

sa_check_bwd bwd_app apply_append [sh_app_1, sh_app_2, sh_app_3] forbid [apply_append_affine, apply_append']

/-! ## Shadows for `apply_append_affine` -/

/-- NL: "under Affine when Q is purely relative" — pointwise, with "purely
relative" spelled out as "every effect of Q is of the form `(none, m)`". -/
theorem sh_apa_1 {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T]
    {M : Type x} [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M))
    (h : ConflictFree (P ⊕ᵢ Q)) (hQ : ∀ a ∈ Q, ∃ m : M, a.effect = ⟨none, m⟩) (θ : τ → T → V)
    (t : τ) (j : T) : apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j := by
  have h1 : (foldAt j (P ++ Q) t).isSome := h t j
  rw [foldAt_append] at h1
  change actOpt (foldAt j (P ++ Q) t) (θ t j) = _
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ' : foldAt j Q t with _ | b
    · simp [hP, hQ'] at h1
    · rw [hP, hQ'] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      have hb : b.abs = none := by
        have hall : ∀ e ∈ effectsAt j Q t, e.abs = none := by
          intro e he
          simp only [effectsAt, List.mem_map, List.mem_filter, mem_active] at he
          obtain ⟨a', ⟨⟨ha', -⟩, -⟩, rfl⟩ := he
          obtain ⟨m, hm⟩ := hQ a' ha'
          rw [hm]
        exact (Affine.fold_abs_none_iff hQ').mpr hall
      exact Affine.act_mul_of_relative (θ t j) hb hc

/-- NL facet: a single purely relative atom appended to a conflict-free program
acts after it. -/
theorem sh_apa_2 {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T]
    {M : Type x} [PCM M] [PCMAction M V] (P : Program τ T (Affine V M)) (q : Atom τ T (Affine V M))
    (h : ConflictFree (P ++ [q])) (hq : q.effect.abs = none) (θ : τ → T → V) :
    apply (P ++ [q]) θ = apply [q] (apply P θ) := by
  funext t j
  apply sh_apa_1 P [q] h _ θ t j
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  exact ⟨a.effect.rel, Affine.ext hq rfl⟩

/-- NL facet: two purely relative programs compose sequentially. -/
theorem sh_apa_3 {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T]
    {M : Type x} [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M))
    (hP : ∀ a ∈ P, a.effect.abs = none) (hQ : ∀ a ∈ Q, a.effect.abs = none)
    (h : ConflictFree (P ++ Q)) (θ : τ → T → V) : apply (P ++ Q) θ = apply Q (apply P θ) := by
  have _ := hP
  funext t j
  exact sh_apa_1 P Q h (fun a ha => ⟨a.effect.rel, Affine.ext (hQ a ha) rfl⟩) θ t j

sa_check_shadow_free sh_apa_1 [apply_append, apply_append_affine, apply_append']
sa_check_shadow_free sh_apa_2 [apply_append, apply_append_affine, apply_append']
sa_check_shadow_free sh_apa_3 [apply_append, apply_append_affine, apply_append']

theorem fwd_apa_1
    (hT : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] {P Q : Program τ T (Affine V M)}, ConflictFree (P ++ Q) →
      (∀ a ∈ Q, a.effect.abs = none) → ∀ (θ : τ → T → V),
      apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M)), ConflictFree (P ⊕ᵢ Q) →
      (∀ a ∈ Q, ∃ m : M, a.effect = ⟨none, m⟩) → ∀ (θ : τ → T → V) (t : τ) (j : T),
      apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j := by
  intro τ T V _ _ M _ _ P Q h hQ θ t j
  have hQ' : ∀ a ∈ Q, a.effect.abs = none := by
    intro a ha
    obtain ⟨m, hm⟩ := hQ a ha
    rw [hm]
  exact congrFun (congrFun (hT h hQ' θ) t) j

sa_check_fwd fwd_apa_1 apply_append_affine sh_apa_1
  forbid [apply_append, apply_append', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_apa_2, sh_apa_3]

theorem fwd_apa_2
    (hT : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] {P Q : Program τ T (Affine V M)}, ConflictFree (P ++ Q) →
      (∀ a ∈ Q, a.effect.abs = none) → ∀ (θ : τ → T → V),
      apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P : Program τ T (Affine V M)) (q : Atom τ T (Affine V M)),
      ConflictFree (P ++ [q]) → q.effect.abs = none → ∀ (θ : τ → T → V),
      apply (P ++ [q]) θ = apply [q] (apply P θ) := by
  intro τ T V _ _ M _ _ P q h hq θ
  apply hT h _ θ
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  exact hq

sa_check_fwd fwd_apa_2 apply_append_affine sh_apa_2
  forbid [apply_append, apply_append', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_apa_1, sh_apa_3]

theorem fwd_apa_3
    (hT : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] {P Q : Program τ T (Affine V M)}, ConflictFree (P ++ Q) →
      (∀ a ∈ Q, a.effect.abs = none) → ∀ (θ : τ → T → V),
      apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M)),
      (∀ a ∈ P, a.effect.abs = none) → (∀ a ∈ Q, a.effect.abs = none) →
      ConflictFree (P ++ Q) → ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ) := by
  intro τ T V _ _ M _ _ P Q _ hQ h θ
  exact hT h hQ θ

sa_check_fwd fwd_apa_3 apply_append_affine sh_apa_3
  forbid [apply_append, apply_append', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_apa_1, sh_apa_2]

theorem bwd_apa
    (h₁ : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M)), ConflictFree (P ⊕ᵢ Q) →
      (∀ a ∈ Q, ∃ m : M, a.effect = ⟨none, m⟩) → ∀ (θ : τ → T → V) (t : τ) (j : T),
      apply (P ⊕ᵢ Q) θ t j = apply Q (apply P θ) t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P : Program τ T (Affine V M)) (q : Atom τ T (Affine V M)),
      ConflictFree (P ++ [q]) → q.effect.abs = none → ∀ (θ : τ → T → V),
      apply (P ++ [q]) θ = apply [q] (apply P θ))
    (h₃ : ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] (P Q : Program τ T (Affine V M)),
      (∀ a ∈ P, a.effect.abs = none) → (∀ a ∈ Q, a.effect.abs = none) →
      ConflictFree (P ++ Q) → ∀ (θ : τ → T → V), apply (P ++ Q) θ = apply Q (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {V : Type w} [LinearOrder τ] [DecidableEq T] {M : Type x}
      [PCM M] [PCMAction M V] {P Q : Program τ T (Affine V M)}, ConflictFree (P ++ Q) →
      (∀ a ∈ Q, a.effect.abs = none) → ∀ (θ : τ → T → V),
      apply (P ++ Q) θ = apply Q (apply P θ) := by
  intro τ T V _ _ M _ _ P Q h hQ θ
  have _ := @h₂
  have _ := @h₃
  funext t j
  exact h₁ P Q h (fun a ha => ⟨a.effect.rel, Affine.ext (hQ a ha) rfl⟩) θ t j

sa_check_bwd bwd_apa apply_append_affine [sh_apa_1, sh_apa_2, sh_apa_3]
  forbid [apply_append, apply_append', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none]

end CategoricalInterventionsProofs.SAPass.C14
