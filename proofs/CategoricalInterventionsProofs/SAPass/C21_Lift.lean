import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Transport

/-!
# SA-Pass claim 21

NL claim: **"Lifting to a stratified model is functorial, preserves
conflict-freeness, and acts stratum-wise."**
Targets: `lift_comp`, `conflictFree_lift_iff'`, `apply_lift`.

Reading note: "functorial" for a list-valued operation means the identity and
composition laws on programs.  Composition holds only up to permutation
(fibres are enumerated in an unspecified order), so the shadow states it as a
`List.Perm`; `lift_comp` states it at the level of folds only.
-/

namespace CategoricalInterventionsProofs.SAPass.C21

open CategoricalInterventionsProofs

universe u v w x y

/-! ## Shadows for `lift_comp` -/

/-- NL: "functorial" — composition law at the level of programs, up to
permutation of atoms. -/
theorem sh_lc_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [Fintype T'] {T'' : Type y} [DecidableEq T''] [Fintype T'']
    (π : T' → T) (π' : T'' → T') (P : Program τ T M) :
    (lift π' (lift π P)).Perm (lift (π ∘ π') P) := by
  induction P with
  | nil => simp [lift]
  | cons a P ih =>
    rw [lift_cons, lift_cons]
    unfold lift at ih ⊢
    rw [List.flatMap_append]
    refine List.Perm.append ?_ ih
    simp only [copies, List.flatMap_map]
    rw [← List.map_flatMap]
    exact (fibre_comp_perm π π' a.target).map _

/-- NL: "functorial" — composition law for the action on schedules. -/
theorem sh_lc_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T'']
    [Fintype T''] {V : Type y} [HasAct M V] (π : T' → T) (π' : T'' → T') (P : Program τ T M)
    (θ : τ → T'' → V) : apply (lift π' (lift π P)) θ = apply (lift (π ∘ π') P) θ := by
  funext t j''
  simp only [apply, foldAt_lift]
  rfl

/-- NL: "functorial" — identity law (at the level of folds). -/
theorem sh_lc_3 {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [PCM M] (P : Program τ T M) (j : T) (t : τ) :
    foldAt j (lift id P) t = foldAt j P t :=
  foldAt_lift id P j t

sa_check_shadow_free sh_lc_1 [lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_lc_2 [lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_lc_3 [lift_comp, conflictFree_lift_iff', apply_lift]

/- `fwd_lc_1` (lift_comp ⇒ sh_lc_1) is OMITTED: fold-level equality does not
determine the atom lists (a trivial action or a trivial algebra forgets them).
`fwd_lc_3` (lift_comp ⇒ sh_lc_3) is OMITTED: the composition law says nothing
about `lift id`.  See SA-PASS.md. -/

theorem fwd_lc_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M) (j'' : T'') (t : τ),
      foldAt j'' (lift π' (lift π P)) t = foldAt j'' (lift (π ∘ π') P) t) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      {V : Type y} [HasAct M V] (π : T' → T) (π' : T'' → T') (P : Program τ T M)
      (θ : τ → T'' → V), apply (lift π' (lift π P)) θ = apply (lift (π ∘ π') P) θ := by
  intro τ T T' M _ _ _ _ _ T'' _ _ V _ π π' P θ
  funext t j''
  simp only [apply]
  rw [hT]

sa_check_fwd fwd_lc_2 lift_comp sh_lc_2 forbid [conflictFree_lift_iff', apply_lift, foldAt_lift, sh_lc_1, sh_lc_3]

/-- Backward: fold equality follows from permutation equivalence. -/
theorem bwd_lc
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M),
      (lift π' (lift π P)).Perm (lift (π ∘ π') P))
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      {V : Type y} [HasAct M V] (π : T' → T) (π' : T'' → T') (P : Program τ T M)
      (θ : τ → T'' → V), apply (lift π' (lift π P)) θ = apply (lift (π ∘ π') P) θ)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [Fintype T] [PCM M] (P : Program τ T M) (j : T) (t : τ),
      foldAt j (lift id P) t = foldAt j P t) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {T'' : Type y} [DecidableEq T''] [Fintype T'']
      (π : T' → T) (π' : T'' → T') (P : Program τ T M) (j'' : T'') (t : τ),
      foldAt j'' (lift π' (lift π P)) t = foldAt j'' (lift (π ∘ π') P) t := by
  intro τ T T' M _ _ _ _ _ T'' _ _ π π' P j'' t
  have _ := @h₂
  have _ := @h₃
  exact foldAt_perm (h₁ π π' P) j'' t

sa_check_bwd bwd_lc lift_comp [sh_lc_1, sh_lc_2, sh_lc_3] forbid [conflictFree_lift_iff', apply_lift, foldAt_lift]

/-! ## Shadows for `conflictFree_lift_iff'` -/

/-- NL: "preserves conflict-freeness" — unconditionally (no hypothesis on `π`). -/
theorem sh_cl_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M)
    (h : ConflictFree P) : ConflictFree (lift π P) := by
  intro t j'
  rw [foldAt_lift]
  exact h t (π j')

/-- NL: "preserves conflict-freeness" — under the theorem's hypothesis that every
used target has a preimage. -/
theorem sh_cl_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M)
    (_hπ : ∀ j ∈ targets P, ∃ j', π j' = j) (h : ConflictFree P) : ConflictFree (lift π P) :=
  sh_cl_1 π P h

sa_check_shadow_free sh_cl_1 [lift_comp, conflictFree_lift_iff', apply_lift, conflictFree_lift, conflictFree_lift_iff]
sa_check_shadow_free sh_cl_2 [lift_comp, conflictFree_lift_iff', apply_lift, conflictFree_lift, conflictFree_lift_iff]

/-- Glue for `fwd_cl_1`: dropping the atoms whose target has an empty fibre does
not change the lift. -/
theorem lift_filter_eq {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [Fintype T'] (π : T' → T) (Q : Program τ T M) :
    lift π Q = lift π (Q.filter (fun a => decide (∃ j', π j' = a.target))) := by
  induction Q with
  | nil => rfl
  | cons a Q ih =>
    rw [lift_cons, List.filter_cons]
    by_cases hex : ∃ j', π j' = a.target
    · simp only [hex, decide_true, if_true]
      rw [lift_cons, ih]
    · have hnil : fibre π a.target = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro j' hj'
        exact hex ⟨j', mem_fibre.mp hj'⟩
      simp only [hex, decide_false, Bool.false_eq_true, if_false]
      rw [hnil, ih]
      rfl

/-- Glue for `fwd_cl_1`: filtering by a predicate that holds on every atom of
target `j` does not change the fold at `j`. -/
theorem foldAt_filter_of {τ : Type u} {T : Type v} {M : Type x} [LinearOrder τ] [DecidableEq T]
    [PCM M] (p : Atom τ T M → Bool) (Q : Program τ T M) (j : T) (t : τ)
    (hp : ∀ a ∈ Q, a.target = j → p a = true) : foldAt j (Q.filter p) t = foldAt j Q t := by
  induction Q with
  | nil => rfl
  | cons a Q ih =>
    have ih := ih (fun b hb e => hp b (List.mem_cons_of_mem _ hb) e)
    rw [List.filter_cons]
    by_cases hpa : p a = true
    · simp only [hpa, if_true]
      rw [foldAt_cons, foldAt_cons, ih]
    · simp only [hpa, Bool.false_eq_true, if_false]
      have hne : a.target ≠ j := fun e => hpa (hp a List.mem_cons_self e)
      rw [foldAt_cons, if_neg (fun h => hne h.2), ih]

theorem fwd_cl_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {π : T' → T} (P : Program τ T M),
      (∀ j ∈ targets P, ∃ j', π j' = j) → (ConflictFree (lift π P) ↔ ConflictFree P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      ConflictFree P → ConflictFree (lift π P) := by
  intro τ T T' M _ _ _ _ _ π P h
  -- restrict to the atoms whose target has a preimage; the lift is unchanged
  rw [lift_filter_eq π P]
  apply (hT _ _).mpr
  · intro t j
    by_cases hj : ∃ j', π j' = j
    · rw [foldAt_filter_of]
      · exact h t j
      · intro a _ e
        rw [e]
        exact decide_eq_true hj
    · rw [foldAt_eq_one_of_none]
      · rfl
      · intro a ha _ e
        rw [List.mem_filter, decide_eq_true_eq] at ha
        exact hj (e ▸ ha.2)
  · intro j ⟨a, ha, e⟩
    rw [List.mem_filter, decide_eq_true_eq] at ha
    exact e ▸ ha.2

sa_check_fwd fwd_cl_1 conflictFree_lift_iff' sh_cl_1
  forbid [lift_comp, apply_lift, foldAt_lift, conflictFree_lift, conflictFree_lift_iff, sh_cl_2]

theorem fwd_cl_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] {π : T' → T} (P : Program τ T M),
      (∀ j ∈ targets P, ∃ j', π j' = j) → (ConflictFree (lift π P) ↔ ConflictFree P)) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [Fintype T'] [PCM M] (π : T' → T) (P : Program τ T M),
      (∀ j ∈ targets P, ∃ j', π j' = j) → ConflictFree P → ConflictFree (lift π P) := by
  intro τ T T' M _ _ _ _ _ π P hπ h
  exact (hT P hπ).mpr h

sa_check_fwd fwd_cl_2 conflictFree_lift_iff' sh_cl_2
  forbid [lift_comp, apply_lift, foldAt_lift, conflictFree_lift, conflictFree_lift_iff, sh_cl_1]

/- `bwd_cl` is OMITTED: the sentence claims only preservation; the theorem also
*reflects* conflict-freeness (an `↔` under the preimage hypothesis), which the
sentence-derived shadows cannot imply.  Note the development does contain the
unconditional preservation theorem `conflictFree_lift`, which is what the
sentence describes.  See SA-PASS.md. -/

/-! ## Shadows for `apply_lift` -/

/-- NL: "acts stratum-wise" — effect level: on stratum `j'` the lifted program
acts on any value exactly as `P` acts on target `π j'`. -/
theorem sh_al_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y}
    [LinearOrder τ] [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V]
    (π : T' → T) (P : Program τ T M) (t : τ) (j' : T') (v : V) :
    actOpt (foldAt j' (lift π P) t) v = actOpt (foldAt (π j') P t) v := by
  rw [foldAt_lift]

/-- NL: "acts stratum-wise" — naturality: on a schedule pulled back from the
base model, lifting then applying is applying then pulling back. -/
theorem sh_al_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y}
    [LinearOrder τ] [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V]
    (π : T' → T) (P : Program τ T M) (θ : τ → T → V) (t : τ) (j' : T') :
    apply (lift π P) (fun t j' => θ t (π j')) t j' = apply P θ t (π j') := by
  simp only [apply, foldAt_lift]

/-- NL facet: strata whose base target `P` never touches are left unchanged. -/
theorem sh_al_3 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y}
    [LinearOrder τ] [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [PCMAction M V]
    (π : T' → T) (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T')
    (h : ∀ a ∈ P, a.target ≠ π j') : apply (lift π P) θ' t j' = θ' t j' := by
  simp only [apply, foldAt_lift]
  rw [foldAt_eq_one_of_none _ _ _ (fun a ha _ e => h a ha e)]
  exact act_one _

sa_check_shadow_free sh_al_1 [lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_al_2 [lift_comp, conflictFree_lift_iff', apply_lift]
sa_check_shadow_free sh_al_3 [lift_comp, conflictFree_lift_iff', apply_lift]

theorem fwd_al_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      apply (lift π P) θ' t j' = actOpt (foldAt (π j') P t) (θ' t j')) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (t : τ) (j' : T') (v : V),
      actOpt (foldAt j' (lift π P) t) v = actOpt (foldAt (π j') P t) v := by
  intro τ T T' M V _ _ _ _ _ _ π P t j' v
  exact hT π P (fun _ _ => v) t j'

sa_check_fwd fwd_al_1 apply_lift sh_al_1 forbid [lift_comp, conflictFree_lift_iff', foldAt_lift, sh_al_2, sh_al_3]

theorem fwd_al_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      apply (lift π P) θ' t j' = actOpt (foldAt (π j') P t) (θ' t j')) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ : τ → T → V) (t : τ) (j' : T'),
      apply (lift π P) (fun t j' => θ t (π j')) t j' = apply P θ t (π j') := by
  intro τ T T' M V _ _ _ _ _ _ π P θ t j'
  rw [hT]
  rfl

sa_check_fwd fwd_al_2 apply_lift sh_al_2 forbid [lift_comp, conflictFree_lift_iff', foldAt_lift, sh_al_1, sh_al_3]

theorem fwd_al_3
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      apply (lift π P) θ' t j' = actOpt (foldAt (π j') P t) (θ' t j')) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [PCMAction M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      (∀ a ∈ P, a.target ≠ π j') → apply (lift π P) θ' t j' = θ' t j' := by
  intro τ T T' M V _ _ _ _ _ _ π P θ' t j' h
  rw [hT, foldAt_eq_one_of_none _ _ _ (fun a ha _ e => h a ha e)]
  exact act_one _

sa_check_fwd fwd_al_3 apply_lift sh_al_3 forbid [lift_comp, conflictFree_lift_iff', foldAt_lift, sh_al_1, sh_al_2]

theorem bwd_al
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (t : τ) (j' : T') (v : V),
      actOpt (foldAt j' (lift π P) t) v = actOpt (foldAt (π j') P t) v)
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ : τ → T → V) (t : τ) (j' : T'),
      apply (lift π P) (fun t j' => θ t (π j')) t j' = apply P θ t (π j'))
    (h₃ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [PCMAction M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      (∀ a ∈ P, a.target ≠ π j') → apply (lift π P) θ' t j' = θ' t j') :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} {V : Type y} [LinearOrder τ]
      [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M] [HasAct M V] (π : T' → T)
      (P : Program τ T M) (θ' : τ → T' → V) (t : τ) (j' : T'),
      apply (lift π P) θ' t j' = actOpt (foldAt (π j') P t) (θ' t j') := by
  intro τ T T' M V _ _ _ _ _ _ π P θ' t j'
  have _ := @h₂
  have _ := @h₃
  exact h₁ π P t j' (θ' t j')

sa_check_bwd bwd_al apply_lift [sh_al_1, sh_al_2, sh_al_3] forbid [lift_comp, conflictFree_lift_iff', foldAt_lift]

end CategoricalInterventionsProofs.SAPass.C21
