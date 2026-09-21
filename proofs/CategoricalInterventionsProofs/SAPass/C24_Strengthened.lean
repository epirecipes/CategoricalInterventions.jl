import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.C02_Order
import CategoricalInterventionsProofs.SAPass.C04_Pairs
import CategoricalInterventionsProofs.SAPass.C06_AffinePCM
import CategoricalInterventionsProofs.SAPass.C20_Pushforward
import CategoricalInterventionsProofs.SAPass.C21_Lift
import CategoricalInterventionsProofs.SAPass.C23_Infer

/-!
# SA-Pass: re-run of the rows with alignment gaps, against the strengthened theorems

Each alignment gap G1–G11 of `design/SA-PASS.md` §4 was closed by adding a
stronger (or one-directional) theorem to the main development.  This file
re-runs the affected rows against the *new* targets, using the shadow sets of
the original files (`C02`, `C04`, `C06`, `C20`, `C21`, `C23`) unchanged, plus
the few extra shadows a new target needs.  The previously omitted checkers
now compile.  (G3, `conflictFree_append_left/right`, was closed by restating
the theorems in place; its checkers live in `C05`.)

| gap | new target | shadows |
|-----|------------|---------|
| G1  | `apply_perm` | `sh_apply_1`, `sh_apply_2` |
| G2  | `disjoint_compatible'` | `sh_dj_1`, `sh_dj_2`, `sh_dj_3` |
| G4, G5 | `two_absolutes_conflict` | `sh_aabs_1`, `sh_aabs_2` |
| G6  | `pushforward_id`; `pushforward_comp` re-scored | `sh_pc_1`; `sh_pc_2`, `sh_pc_3` |
| G7  | `conflictFree_pushforward_of_injOn'` | `sh_cp_1`, `sh_cp_2` |
| G8  | `lift_comp_perm` | `sh_lc_1`, `sh_lc_2` |
| G9  | `lift_id` | `sh_lc_3`, `sh_li_1`, `sh_li_2` |
| G10 | `conflictFree_lift` | `sh_cl_1`, `sh_cl_2` |
| G11 | `infer_putget_schedule` | `sh_ip_1`, `sh_ips_2`, `sh_ips_3` |
-/

namespace CategoricalInterventionsProofs.SAPass.C24

open CategoricalInterventionsProofs
open CategoricalInterventionsProofs.SAPass.C02 (sh_apply_1 sh_apply_2)
open CategoricalInterventionsProofs.SAPass.C04 (sh_dj_1 sh_dj_2 sh_dj_3)
open CategoricalInterventionsProofs.SAPass.C06 (sh_aabs_1 sh_aabs_2)
open CategoricalInterventionsProofs.SAPass.C20 (sh_pc_1 sh_pc_2 sh_pc_3 sh_cp_1 sh_cp_2)
open CategoricalInterventionsProofs.SAPass.C21 (sh_lc_1 sh_lc_2 sh_lc_3 sh_cl_1 sh_cl_2)
open CategoricalInterventionsProofs.SAPass.C23 (sh_ip_1)

universe u v w x y

/-! ## G1: `apply_perm` (claim 2) -/

sa_check_shadow_free sh_apply_1 [apply_perm, apply_comm, fold_perm, foldAt_perm]
sa_check_shadow_free sh_apply_2 [apply_perm, apply_comm, fold_perm, foldAt_perm]

theorem fwd_apply'_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P Q : Program τ T M}, P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P Q : Program τ T M), P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ := by
  intro τ T M V _ _ _ _ P Q h θ
  exact hT h θ

sa_check_fwd fwd_apply'_1 apply_perm sh_apply_1 forbid [apply_comm, fold_perm, foldAt_perm, sh_apply_2]

theorem fwd_apply'_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P Q : Program τ T M}, P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M) (n : ℕ) (θ : τ → T → V),
      apply (P.rotate n) θ = apply P θ := by
  intro τ T M V _ _ _ _ P n θ
  exact hT (List.rotate_perm P n) θ

sa_check_fwd fwd_apply'_2 apply_perm sh_apply_2 forbid [apply_comm, fold_perm, foldAt_perm, sh_apply_1]

theorem bwd_apply'
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P Q : Program τ T M), P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M) (n : ℕ) (θ : τ → T → V),
      apply (P.rotate n) θ = apply P θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {P Q : Program τ T M}, P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ := by
  intro τ T M V _ _ _ _ P Q h θ
  have _ := @h₂
  exact h₁ P Q h θ

sa_check_bwd bwd_apply' apply_perm [sh_apply_1, sh_apply_2] forbid [apply_comm, fold_perm, foldAt_perm]

/-! ## G2: `disjoint_compatible'` (claim 4) -/

sa_check_shadow_free sh_dj_1 [disjoint_compatible', disjoint_compatible, different_target_compatible, conflictFree_pair]
sa_check_shadow_free sh_dj_2 [disjoint_compatible', disjoint_compatible, different_target_compatible, conflictFree_pair]
sa_check_shadow_free sh_dj_3 [disjoint_compatible', disjoint_compatible, different_target_compatible, conflictFree_pair]

theorem fwd_dj'_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M), (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b h
  exact hT h

sa_check_fwd fwd_dj'_1 disjoint_compatible' sh_dj_1
  forbid [disjoint_compatible, different_target_compatible, conflictFree_pair, sh_dj_2, sh_dj_3]

theorem fwd_dj'_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (s s' : Span τ), a.support = .span s → b.support = .span s' →
      s.hi ≤ s'.lo ∨ s'.hi ≤ s.lo → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b s s' ha hb h
  apply hT
  intro t ⟨hta, htb⟩
  rw [ha] at hta
  rw [hb] at htb
  rcases h with h | h
  · exact absurd (lt_of_lt_of_le hta.2 (le_trans h htb.1)) (lt_irrefl t)
  · exact absurd (lt_of_lt_of_le htb.2 (le_trans h hta.1)) (lt_irrefl t)

sa_check_fwd fwd_dj'_2 disjoint_compatible' sh_dj_2
  forbid [disjoint_compatible, different_target_compatible, conflictFree_pair, sh_dj_1, sh_dj_3]

theorem fwd_dj'_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j : T) (s s' : Span τ) (e₁ e₂ : E), s.Disjoint s' →
      ConflictFree [(⟨i₁, j, .span s, Reject.eff e₁⟩ : Atom τ T (Reject E)),
        ⟨i₂, j, .span s', Reject.eff e₂⟩] := by
  intro τ T E _ _ i₁ i₂ j s s' e₁ e₂ h
  apply hT
  intro t ⟨hta, htb⟩
  exact h.not_mem hta htb

sa_check_fwd fwd_dj'_3 disjoint_compatible' sh_dj_3
  forbid [disjoint_compatible, different_target_compatible, conflictFree_pair, sh_dj_1, sh_dj_2]

theorem bwd_dj'
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M), (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b])
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (s s' : Span τ), a.support = .span s → b.support = .span s' →
      s.hi ≤ s'.lo ∨ s'.hi ≤ s.lo → ConflictFree [a, b])
    (h₃ : ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j : T) (s s' : Span τ) (e₁ e₂ : E), s.Disjoint s' →
      ConflictFree [(⟨i₁, j, .span s, Reject.eff e₁⟩ : Atom τ T (Reject E)),
        ⟨i₂, j, .span s', Reject.eff e₂⟩]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b h
  have _ := @h₂
  have _ := @h₃
  exact h₁ a b h

sa_check_bwd bwd_dj' disjoint_compatible' [sh_dj_1, sh_dj_2, sh_dj_3]
  forbid [disjoint_compatible, different_target_compatible, conflictFree_pair]

/-! ## G4, G5: `two_absolutes_conflict` (claim 6) -/

sa_check_shadow_free sh_aabs_1 [two_absolutes_conflict, affine_pcm, fold_affine_isSome_iff, Affine.mul_eq_none_of_abs]
sa_check_shadow_free sh_aabs_2 [two_absolutes_conflict, affine_pcm, fold_affine_isSome_iff, Affine.mul_eq_none_of_abs]

theorem fwd_aabs'_1
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] {l : List (Affine V M)} {a b : Affine V M},
      [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none) :
    ∀ {V : Type u} {M : Type v} [PCM M] (a b : Affine V M),
      a.abs.isSome → b.abs.isSome → mul a b = none := by
  intro V M _ a b ha hb
  have := hT (List.Sublist.refl [a, b]) ha hb
  rwa [foldList_cons, foldList_singleton, Option.bind_some] at this

sa_check_fwd fwd_aabs'_1 two_absolutes_conflict sh_aabs_1
  forbid [affine_pcm, fold_affine_isSome_iff, fold_pairwise_affine, Affine.mul_eq_none_of_abs,
    Affine.fold_abs_isSome_of_mem, sh_aabs_2]

theorem fwd_aabs'_2
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] {l : List (Affine V M)} {a b : Affine V M},
      [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMTotal M] (l : List (Affine V M)) (a b : Affine V M),
      [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none := by
  intro V M _ _ l a b hab ha hb
  exact hT hab ha hb

sa_check_fwd fwd_aabs'_2 two_absolutes_conflict sh_aabs_2
  forbid [affine_pcm, fold_affine_isSome_iff, fold_pairwise_affine, Affine.mul_eq_none_of_abs,
    Affine.fold_abs_isSome_of_mem, sh_aabs_1]

/-- Backward: from the two-element statement by induction on the sublist; the
glue `Affine.fold_abs_none_iff` (an absolute is present in a defined fold iff it
is present in some element) is a fact about the definition of the fold. -/
theorem bwd_aabs'
    (h₁ : ∀ {V : Type u} {M : Type v} [PCM M] (a b : Affine V M),
      a.abs.isSome → b.abs.isSome → mul a b = none)
    (h₂ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMTotal M] (l : List (Affine V M))
      (a b : Affine V M), [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none) :
    ∀ {V : Type u} {M : Type v} [PCM M] {l : List (Affine V M)} {a b : Affine V M},
      [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none := by
  intro V M _ l a b hab ha hb
  have _ := @h₂
  induction l with
  | nil => simp at hab
  | cons x l ih =>
    rw [foldList_cons]
    rcases List.sublist_cons_iff.mp hab with h | ⟨r, hr, hr'⟩
    · rw [ih h]; rfl
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
      have hbl : b ∈ l := hr'.subset List.mem_cons_self
      rcases hl : foldList l with _ | c
      · rfl
      · simp only [Option.bind_some]
        apply h₁ a c ha
        by_contra hc
        have hc' : c.abs = none := by
          cases hx : c.abs with
          | none => rfl
          | some _ => exact absurd (by simp [hx]) hc
        have := (Affine.fold_abs_none_iff hl).mp hc' b hbl
        simp [this] at hb

sa_check_bwd bwd_aabs' two_absolutes_conflict [sh_aabs_1, sh_aabs_2]
  forbid [affine_pcm, fold_affine_isSome_iff, fold_pairwise_affine, Affine.mul_eq_none_of_abs,
    Affine.fold_abs_isSome_of_mem]

/-! ## G6: `pushforward_id`, and `pushforward_comp` re-scored (claim 20) -/

sa_check_shadow_free sh_pc_1 [pushforward_id, pushforward_comp, conflictFree_pushforward_of_injOn, conflictFree_pushforward_of_injOn']

theorem fwd_pid_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      pushforward id P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      pushforward id P = P := by
  intro τ T M _ P
  exact hT P

sa_check_fwd fwd_pid_1 pushforward_id sh_pc_1
  forbid [pushforward_comp, conflictFree_pushforward_of_injOn, conflictFree_pushforward_of_injOn', sh_pc_2, sh_pc_3]

theorem bwd_pid
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      pushforward id P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      pushforward id P = P := by
  intro τ T M _ P
  exact h₁ P

sa_check_bwd bwd_pid pushforward_id [sh_pc_1]
  forbid [pushforward_comp, conflictFree_pushforward_of_injOn, conflictFree_pushforward_of_injOn']

/-- `pushforward_comp` re-scored with the identity-law shadow moved to
`pushforward_id`: the composition law is implied by its two remaining facets. -/
theorem bwd_pc'
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
  have _ := @h₂
  exact List.ext_getElem? (h₃ f g P)

sa_check_bwd bwd_pc' pushforward_comp [sh_pc_2, sh_pc_3]
  forbid [pushforward_id, conflictFree_pushforward_of_injOn, conflictFree_pushforward_of_injOn', sh_pc_1]

/-! ## G7: `conflictFree_pushforward_of_injOn'` (claim 20) -/

sa_check_shadow_free sh_cp_1 [conflictFree_pushforward_of_injOn', conflictFree_pushforward_of_injOn, pushforward_comp, pushforward_id]
sa_check_shadow_free sh_cp_2 [conflictFree_pushforward_of_injOn', conflictFree_pushforward_of_injOn, pushforward_comp, pushforward_id]

theorem fwd_cp'_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] {f : T → T'} {P : Program τ T M}, Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P) := by
  intro τ T T' M _ _ _ _ f P hf h
  exact hT hf h

sa_check_fwd fwd_cp'_1 conflictFree_pushforward_of_injOn' sh_cp_1
  forbid [conflictFree_pushforward_of_injOn, pushforward_comp, pushforward_id, sh_cp_2]

theorem fwd_cp'_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] {f : T → T'} {P : Program τ T M}, Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Function.Injective f →
      ConflictFree P → ConflictFree (pushforward f P) := by
  intro τ T T' M _ _ _ _ f P hf h
  exact hT hf.injOn h

sa_check_fwd fwd_cp'_2 conflictFree_pushforward_of_injOn' sh_cp_2
  forbid [conflictFree_pushforward_of_injOn, pushforward_comp, pushforward_id, sh_cp_1]

theorem bwd_cp'
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P))
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (f : T → T') (P : Program τ T M), Function.Injective f →
      ConflictFree P → ConflictFree (pushforward f P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] {f : T → T'} {P : Program τ T M}, Set.InjOn f (targets P) →
      ConflictFree P → ConflictFree (pushforward f P) := by
  intro τ T T' M _ _ _ _ f P hf h
  have _ := @h₂
  exact h₁ f P hf h

sa_check_bwd bwd_cp' conflictFree_pushforward_of_injOn' [sh_cp_1, sh_cp_2]
  forbid [conflictFree_pushforward_of_injOn, pushforward_comp, pushforward_id]

/-! ## G8: `lift_comp_perm` (claim 21) -/

sa_check_shadow_free sh_lc_1 [lift_comp_perm, lift_id, lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_lc_2 [lift_comp_perm, lift_id, lift_comp, conflictFree_lift_iff', apply_lift]

theorem fwd_lcp_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [Fintype T'] {T'' : Type y} [DecidableEq T'] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P) := by
  intro τ T T' M _ _ _ _ T'' _ _ π π' P
  exact hT π π' P

sa_check_fwd fwd_lcp_1 lift_comp_perm sh_lc_1
  forbid [lift_comp, lift_id, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_comp_perm, sh_lc_2]

theorem fwd_lcp_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [Fintype T'] {T'' : Type y} [DecidableEq T'] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      {V : Type y} [HasAct M V] (π : T' → T) (π' : T'' → T') (P : Program τ T M)
      (θ : τ → T'' → V), apply (lift π' (lift π P)) θ = apply (lift (π ∘ π') P) θ := by
  intro τ T T' M _ _ _ _ _ T'' _ _ V _ π π' P θ
  funext t j''
  simp only [apply]
  rw [foldAt_perm (hT π π' P)]

sa_check_fwd fwd_lcp_2 lift_comp_perm sh_lc_2
  forbid [lift_comp, lift_id, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_comp_perm, sh_lc_1]

theorem bwd_lcp
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P))
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      {V : Type y} [HasAct M V] (π : T' → T) (π' : T'' → T') (P : Program τ T M)
      (θ : τ → T'' → V), apply (lift π' (lift π P)) θ = apply (lift (π ∘ π') P) θ) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [Fintype T'] {T'' : Type y} [DecidableEq T'] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P) := by
  intro τ T T' M _ _ _ T'' _ _ π π' P
  have _ := @h₂
  classical
  exact h₁ π π' P

sa_check_bwd bwd_lcp lift_comp_perm [sh_lc_1, sh_lc_2]
  forbid [lift_comp, lift_id, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_comp_perm]

/-! ## G9: `lift_id` (claim 21) -/

/-- NL: "functorial" — identity law, position-wise (a list-level facet, since
fold equality does not determine the atom list). -/
theorem sh_li_1 {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T]
    [Fintype T] (P : Program τ T M) (i : ℕ) : (lift id P)[i]? = P[i]? := by
  induction P generalizing i with
  | nil => rfl
  | cons a P ih =>
    rw [lift_cons, fibre_id]
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- NL: "functorial" — identity law, membership form. -/
theorem sh_li_2 {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T]
    [Fintype T] (P : Program τ T M) (a : Atom τ T M) : a ∈ lift id P ↔ a ∈ P := by
  induction P with
  | nil => rfl
  | cons b P ih =>
    rw [lift_cons, fibre_id]
    show a ∈ [b] ++ lift id P ↔ a ∈ b :: P
    rw [List.singleton_append, List.mem_cons, List.mem_cons, ih]

sa_check_shadow_free sh_lc_3 [lift_id, lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_li_1 [lift_id, lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_li_2 [lift_id, lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift]

theorem fwd_li_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M), lift id P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M) (i : ℕ), (lift id P)[i]? = P[i]? := by
  intro τ T M _ _ _ P i
  rw [hT]

sa_check_fwd fwd_li_1 lift_id sh_li_1
  forbid [lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_id, sh_li_2, sh_lc_3]

theorem fwd_li_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M), lift id P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M) (a : Atom τ T M), a ∈ lift id P ↔ a ∈ P := by
  intro τ T M _ _ _ P a
  rw [hT]

sa_check_fwd fwd_li_2 lift_id sh_li_2
  forbid [lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_id, sh_li_1, sh_lc_3]

theorem fwd_li_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M), lift id P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T] [PCM M]
      (P : Program τ T M) (j : T) (t : τ), foldAt j (lift id P) t = foldAt j P t := by
  intro τ T M _ _ _ _ P j t
  rw [hT]

sa_check_fwd fwd_li_3 lift_id sh_lc_3
  forbid [lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_id, sh_li_1, sh_li_2]

theorem bwd_li
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M) (i : ℕ), (lift id P)[i]? = P[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M) (a : Atom τ T M), a ∈ lift id P ↔ a ∈ P)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [PCM M] (P : Program τ T M) (j : T) (t : τ), foldAt j (lift id P) t = foldAt j P t) :
    ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T] [Fintype T]
      (P : Program τ T M), lift id P = P := by
  intro τ T M _ _ _ P
  have _ := @h₂
  have _ := @h₃
  exact List.ext_getElem? (h₁ P)

sa_check_bwd bwd_li lift_id [sh_li_1, sh_li_2, sh_lc_3]
  forbid [lift_comp_perm, lift_comp, conflictFree_lift_iff', apply_lift, foldAt_lift, fibre_id]

/-! ## G10: `conflictFree_lift` (claim 21) -/

sa_check_shadow_free sh_cl_1 [conflictFree_lift, conflictFree_lift_iff', conflictFree_lift_iff, lift_comp, apply_lift]
sa_check_shadow_free sh_cl_2 [conflictFree_lift, conflictFree_lift_iff', conflictFree_lift_iff, lift_comp, apply_lift]

theorem fwd_cl'_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {π : T' → T} {P : Program τ T M},
      ConflictFree P → ConflictFree (lift π P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      ConflictFree P → ConflictFree (lift π P) := by
  intro τ T T' M _ _ _ _ _ π P h
  exact hT h

sa_check_fwd fwd_cl'_1 conflictFree_lift sh_cl_1
  forbid [conflictFree_lift_iff', conflictFree_lift_iff, lift_comp, apply_lift, foldAt_lift, sh_cl_2]

theorem fwd_cl'_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {π : T' → T} {P : Program τ T M},
      ConflictFree P → ConflictFree (lift π P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      (∀ j ∈ targets P, ∃ j', π j' = j) → ConflictFree P → ConflictFree (lift π P) := by
  intro τ T T' M _ _ _ _ _ π P _ h
  exact hT h

sa_check_fwd fwd_cl'_2 conflictFree_lift sh_cl_2
  forbid [conflictFree_lift_iff', conflictFree_lift_iff, lift_comp, apply_lift, foldAt_lift, sh_cl_1]

theorem bwd_cl'
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      ConflictFree P → ConflictFree (lift π P))
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      (∀ j ∈ targets P, ∃ j', π j' = j) → ConflictFree P → ConflictFree (lift π P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {π : T' → T} {P : Program τ T M},
      ConflictFree P → ConflictFree (lift π P) := by
  intro τ T T' M _ _ _ _ _ π P h
  have _ := @h₂
  exact h₁ π P h

sa_check_bwd bwd_cl' conflictFree_lift [sh_cl_1, sh_cl_2]
  forbid [conflictFree_lift_iff', conflictFree_lift_iff, lift_comp, apply_lift, foldAt_lift]

/-! ## G11: `infer_putget_schedule` (claim 23) -/

/-- NL: "returns that output" — at the start of every epoch, as a whole
target-vector (instance of the schedule reading at `e.lo`). -/
theorem sh_ips_2 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (P : Program τ T (Multiplicative G)) (hP : SpanOnly P)
    (θ0 : T → G) (e : Span τ) (he : e ∈ epochs P) :
    apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) e.lo =
      apply P (fun _ => θ0) e.lo := by
  funext j
  exact sh_ip_1 P hP θ0 e he e.lo (span_lo_mem e) j

/-- NL: "returns that output" — on each epoch the re-applied schedule *is* the
output, as functions restricted to the epoch (`Set.EqOn`). -/
theorem sh_ips_3 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (P : Program τ T (Multiplicative G)) (hP : SpanOnly P)
    (θ0 : T → G) (e : Span τ) (he : e ∈ epochs P) :
    Set.EqOn (apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0))
      (apply P (fun _ => θ0)) e.memSet := by
  intro t ht
  funext j
  exact sh_ip_1 P hP θ0 e he t ht j

sa_check_shadow_free sh_ip_1 [infer_putget_schedule, infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]
sa_check_shadow_free sh_ips_2 [infer_putget_schedule, infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]
sa_check_shadow_free sh_ips_3 [infer_putget_schedule, infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]

theorem fwd_ips_1
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {P : Program τ T (Multiplicative G)}, SpanOnly P → ∀ (θ0 : T → G)
      {e : Span τ}, e ∈ epochs P → ∀ {t : τ}, e.mem t →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t =
        apply P (fun _ => θ0) t) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (c : Span τ), c ∈ epochs P → ∀ (t : τ), c.mem t → ∀ (j : T),
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t j =
        apply P (fun _ => θ0) t j := by
  intro τ T G _ _ _ _ P hP θ0 c hc t ht j
  exact congrFun (hT hP θ0 hc ht) j

sa_check_fwd fwd_ips_1 infer_putget_schedule sh_ip_1
  forbid [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full,
    foldAt_infer, foldAt_infer_mem, sh_ips_2, sh_ips_3]

theorem fwd_ips_2
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {P : Program τ T (Multiplicative G)}, SpanOnly P → ∀ (θ0 : T → G)
      {e : Span τ}, e ∈ epochs P → ∀ {t : τ}, e.mem t →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t =
        apply P (fun _ => θ0) t) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (e : Span τ), e ∈ epochs P →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) e.lo =
        apply P (fun _ => θ0) e.lo := by
  intro τ T G _ _ _ _ P hP θ0 e he
  exact hT hP θ0 he (span_lo_mem e)

sa_check_fwd fwd_ips_2 infer_putget_schedule sh_ips_2
  forbid [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full,
    foldAt_infer, foldAt_infer_mem, sh_ip_1, sh_ips_3]

theorem fwd_ips_3
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {P : Program τ T (Multiplicative G)}, SpanOnly P → ∀ (θ0 : T → G)
      {e : Span τ}, e ∈ epochs P → ∀ {t : τ}, e.mem t →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t =
        apply P (fun _ => θ0) t) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (e : Span τ), e ∈ epochs P →
      Set.EqOn (apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0))
        (apply P (fun _ => θ0)) e.memSet := by
  intro τ T G _ _ _ _ P hP θ0 e he t ht
  exact hT hP θ0 he ht

sa_check_fwd fwd_ips_3 infer_putget_schedule sh_ips_3
  forbid [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full,
    foldAt_infer, foldAt_infer_mem, sh_ip_1, sh_ips_2]

theorem bwd_ips
    (h₁ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (c : Span τ), c ∈ epochs P → ∀ (t : τ), c.mem t → ∀ (j : T),
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t j =
        apply P (fun _ => θ0) t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (e : Span τ), e ∈ epochs P →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) e.lo =
        apply P (fun _ => θ0) e.lo)
    (h₃ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (e : Span τ), e ∈ epochs P →
      Set.EqOn (apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0))
        (apply P (fun _ => θ0)) e.memSet) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {P : Program τ T (Multiplicative G)}, SpanOnly P → ∀ (θ0 : T → G)
      {e : Span τ}, e ∈ epochs P → ∀ {t : τ}, e.mem t →
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t =
        apply P (fun _ => θ0) t := by
  intro τ T G _ _ _ _ P hP θ0 e he t ht
  have _ := @h₂
  have _ := @h₃
  funext j
  exact h₁ P hP θ0 e he t ht j

sa_check_bwd bwd_ips infer_putget_schedule [sh_ip_1, sh_ips_2, sh_ips_3]
  forbid [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full,
    foldAt_infer, foldAt_infer_mem]

end CategoricalInterventionsProofs.SAPass.C24
