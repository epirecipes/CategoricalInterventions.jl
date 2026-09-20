import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Transport

/-!
# SA-Pass claim 20

NL claim: **"Pushforward is functorial and preserves conflict-freeness when
injective on the targets used."**
Targets: `pushforward_comp`, `conflictFree_pushforward_of_injOn`.
-/

namespace CategoricalInterventionsProofs.SAPass.C20

open CategoricalInterventionsProofs

universe u v w x y

/-! ## Shadows for `pushforward_comp` -/

/-- NL: "functorial" — the identity law: pushing forward along `id` is the
identity on programs. -/
theorem sh_pc_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) :
    pushforward id P = P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    show (⟨a.id, a.target, a.support, a.effect⟩ : Atom τ T M) :: pushforward id P = a :: P
    rw [ih]

/-- NL: "functorial" — the composition law, atom-membership form. -/
theorem sh_pc_2 {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y}
    [LinearOrder τ] (f : T → T') (g : T' → T'') (P : Program τ T M) (b : Atom τ T'' M) :
    b ∈ pushforward g (pushforward f P) ↔ b ∈ pushforward (g ∘ f) P := by
  have : pushforward g (pushforward f P) = pushforward (g ∘ f) P := by
    simp [pushforward, List.map_map, Function.comp_def]
  rw [this]

/-- NL: "functorial" — the composition law, position-wise. -/
theorem sh_pc_3 {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y}
    [LinearOrder τ] (f : T → T') (g : T' → T'') (P : Program τ T M) (i : ℕ) :
    (pushforward g (pushforward f P))[i]? = (pushforward (g ∘ f) P)[i]? := by
  have : pushforward g (pushforward f P) = pushforward (g ∘ f) P := by
    simp [pushforward, List.map_map, Function.comp_def]
  rw [this]

sa_check_shadow_free sh_pc_1 [pushforward_comp, conflictFree_pushforward_of_injOn]
sa_check_shadow_free sh_pc_2 [pushforward_comp, conflictFree_pushforward_of_injOn]
sa_check_shadow_free sh_pc_3 [pushforward_comp, conflictFree_pushforward_of_injOn]

/- `fwd_pc_1` (pushforward_comp ⇒ sh_pc_1) is OMITTED: the composition law says
nothing about `pushforward id`; the identity law is the other half of
"functorial" and is not stated in the development.  See SA-PASS.md. -/

theorem fwd_pc_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M),
      pushforward g (pushforward f P) = pushforward (g ∘ f) P) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M) (b : Atom τ T'' M),
      b ∈ pushforward g (pushforward f P) ↔ b ∈ pushforward (g ∘ f) P := by
  intro τ T T' T'' M _ f g P b
  rw [hT]

sa_check_fwd fwd_pc_2 pushforward_comp sh_pc_2 forbid [conflictFree_pushforward_of_injOn, sh_pc_1, sh_pc_3]

theorem fwd_pc_3
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M),
      pushforward g (pushforward f P) = pushforward (g ∘ f) P) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M) (i : ℕ),
      (pushforward g (pushforward f P))[i]? = (pushforward (g ∘ f) P)[i]? := by
  intro τ T T' T'' M _ f g P i
  rw [hT]

sa_check_fwd fwd_pc_3 pushforward_comp sh_pc_3 forbid [conflictFree_pushforward_of_injOn, sh_pc_1, sh_pc_2]

theorem bwd_pc
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      pushforward id P = P)
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M) (b : Atom τ T'' M),
      b ∈ pushforward g (pushforward f P) ↔ b ∈ pushforward (g ∘ f) P)
    (h₃ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M) (i : ℕ),
      (pushforward g (pushforward f P))[i]? = (pushforward (g ∘ f) P)[i]?) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {T'' : Type x} {M : Type y} [LinearOrder τ]
      (f : T → T') (g : T' → T'') (P : Program τ T M),
      pushforward g (pushforward f P) = pushforward (g ∘ f) P := by
  intro τ T T' T'' M _ f g P
  have _ := @h₁
  have _ := @h₂
  exact List.ext_getElem? (h₃ f g P)

sa_check_bwd bwd_pc pushforward_comp [sh_pc_1, sh_pc_2, sh_pc_3] forbid [conflictFree_pushforward_of_injOn]

/-! ## Shadows for `conflictFree_pushforward_of_injOn` -/

/-- NL: "preserves conflict-freeness when injective on the targets used". -/
theorem sh_cp_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M)
    (hf : Set.InjOn f (targets P)) (h : ConflictFree P) : ConflictFree (pushforward f P) := by
  intro t j'
  by_cases hj : ∃ a ∈ P, f a.target = j'
  · obtain ⟨a, ha, rfl⟩ := hj
    rw [foldAt_pushforward_of (f := f) (fun b hb e => hf ⟨b, hb, rfl⟩ ⟨a, ha, rfl⟩ e) t]
    exact h t a.target
  · push Not at hj
    rw [foldAt_eq_one_of_none j' (pushforward f P) t]
    · rfl
    · intro b hb _ e
      obtain ⟨a, ha, rfl⟩ := mem_pushforward.mp hb
      exact hj a ha e

/-- NL facet: in particular a globally injective renaming preserves
conflict-freeness. -/
theorem sh_cp_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M)
    (hf : Function.Injective f) (h : ConflictFree P) : ConflictFree (pushforward f P) :=
  sh_cp_1 f P hf.injOn h

sa_check_shadow_free sh_cp_1 [pushforward_comp, conflictFree_pushforward_of_injOn]
sa_check_shadow_free sh_cp_2 [pushforward_comp, conflictFree_pushforward_of_injOn]

theorem fwd_cp_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] {f : T → T'} {P : Program τ T M}, Set.InjOn f (targets P) →
      (ConflictFree (pushforward f P) ↔ ConflictFree P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P) := by
  intro τ T T' M _ _ _ _ f P hf h
  exact (hT hf).mpr h

sa_check_fwd fwd_cp_1 conflictFree_pushforward_of_injOn sh_cp_1 forbid [pushforward_comp, sh_cp_2]

theorem fwd_cp_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] {f : T → T'} {P : Program τ T M}, Set.InjOn f (targets P) →
      (ConflictFree (pushforward f P) ↔ ConflictFree P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Function.Injective f →
      ConflictFree P → ConflictFree (pushforward f P) := by
  intro τ T T' M _ _ _ _ f P hf h
  exact (hT hf.injOn).mpr h

sa_check_fwd fwd_cp_2 conflictFree_pushforward_of_injOn sh_cp_2 forbid [pushforward_comp, sh_cp_1]

/- `bwd_cp` is OMITTED: the sentence claims only preservation; the theorem is an
`↔` (it also *reflects* conflict-freeness), which the sentence-derived shadow
set cannot imply.  See SA-PASS.md. -/

end CategoricalInterventionsProofs.SAPass.C20
