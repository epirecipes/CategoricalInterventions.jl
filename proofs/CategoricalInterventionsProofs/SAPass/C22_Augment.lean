import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Augment

/-!
# SA-Pass claim 22

NL claim: **"A flow is a parameter intervention on the augmented model, unchanged
on the original targets."**
Targets: `augment_restrict`, `augment_conflictFree_iff`.
-/

namespace CategoricalInterventionsProofs.SAPass.C22

open CategoricalInterventionsProofs

universe u v w x y

/-- Glue: a re-proof from the definitions that the augmented fold on an old
target is the original fold (used by the shadows only). -/
theorem restrict_fold {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T)
    (t : τ) : foldAt (Sum.inl j) (augment P Q) t = foldAt j P t := by
  rw [augment, foldAt_append, foldAt_pushforward_of_injective Sum.inl_injective,
    foldAt_eq_one_of_none (Sum.inl j) (pushforward Sum.inr Q) t]
  · rcases foldAt j P t with _ | x <;> simp [mul_one]
  · intro b hb _ e
    obtain ⟨a, -, rfl⟩ := mem_pushforward.mp hb
    exact Sum.inr_ne_inl e

/-! ## Shadows for `augment_restrict` -/

/-- NL: "unchanged on the original targets" — at the level of schedules: on an
old target the augmented program acts exactly as `P` does. -/
theorem sh_ar_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T)
    (t : τ) (V : Type y) [HasAct M V] (θ : τ → (T ⊕ T') → V) :
    apply (augment P Q) θ t (Sum.inl j) = apply P (fun t j => θ t (Sum.inl j)) t j := by
  simp only [apply, restrict_fold]

/-- NL: "a flow is a parameter intervention on the augmented model" — for the
augmentation by a single flow atom on a fresh target, old targets keep their
folds.  (Stated for a fresh target `j' : T'` rather than `augmentFlow`'s `Unit`,
whose universe `0` cannot be reached from a universe-fixed hypothesis.) -/
theorem sh_ar_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M)
    (j : T) (t : τ) : foldAt (Sum.inl j) (augment P [⟨0, j', s, e⟩]) t = foldAt j P t :=
  restrict_fold P _ j t

/-- NL: "unchanged on the original targets" — no action on any value type can
distinguish the augmented program from `P` on an old target. -/
theorem sh_ar_3 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T)
    (t : τ) (V : Type x) [HasAct M V] (v : V) :
    actOpt (foldAt (Sum.inl j) (augment P Q) t) v = actOpt (foldAt j P t) v := by
  rw [restrict_fold]

sa_check_shadow_free sh_ar_1 [augment_restrict, augment_conflictFree_iff]
sa_check_shadow_free sh_ar_2 [augment_restrict, augment_conflictFree_iff]
sa_check_shadow_free sh_ar_3 [augment_restrict, augment_conflictFree_iff]

theorem fwd_ar_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P Q) t = foldAt j P t) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ)
      (V : Type y) [HasAct M V] (θ : τ → (T ⊕ T') → V),
      apply (augment P Q) θ t (Sum.inl j) = apply P (fun t j => θ t (Sum.inl j)) t j := by
  intro τ T T' M _ _ _ _ P Q j t V _ θ
  simp only [apply]
  rw [hT]

sa_check_fwd fwd_ar_1 augment_restrict sh_ar_1 forbid [augment_conflictFree_iff, restrict_fold, sh_ar_2, sh_ar_3]

theorem fwd_ar_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P Q) t = foldAt j P t) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P [⟨0, j', s, e⟩]) t = foldAt j P t := by
  intro τ T T' M _ _ _ _ P j' s e j t
  exact hT P [⟨0, j', s, e⟩] j t

sa_check_fwd fwd_ar_2 augment_restrict sh_ar_2 forbid [augment_conflictFree_iff, restrict_fold, sh_ar_1, sh_ar_3]

theorem fwd_ar_3
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P Q) t = foldAt j P t) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ)
      (V : Type x) [HasAct M V] (v : V),
      actOpt (foldAt (Sum.inl j) (augment P Q) t) v = actOpt (foldAt j P t) v := by
  intro τ T T' M _ _ _ _ P Q j t V _ v
  rw [hT]

sa_check_fwd fwd_ar_3 augment_restrict sh_ar_3 forbid [augment_conflictFree_iff, restrict_fold, sh_ar_1, sh_ar_2]

/-- Backward: instantiate the "no action can tell" shadow with the recording
action `act m _ := some m` on `Option M`, which reads the fold back. -/
theorem bwd_ar
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ)
      (V : Type y) [HasAct M V] (θ : τ → (T ⊕ T') → V),
      apply (augment P Q) θ t (Sum.inl j) = apply P (fun t j => θ t (Sum.inl j)) t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P [⟨0, j', s, e⟩]) t = foldAt j P t)
    (h₃ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ)
      (V : Type x) [HasAct M V] (v : V),
      actOpt (foldAt (Sum.inl j) (augment P Q) t) v = actOpt (foldAt j P t) v) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ),
      foldAt (Sum.inl j) (augment P Q) t = foldAt j P t := by
  intro τ T T' M _ _ _ _ P Q j t
  have _ := @h₁
  have _ := @h₂
  letI inst : HasAct M (Option M) := ⟨fun m _ => some m⟩
  have key : ∀ o : Option M, actOpt (M := M) (V := Option M) o none = o := by
    intro o
    cases o <;> rfl
  have := h₃ P Q j t (Option M) none
  rwa [key, key] at this

sa_check_bwd bwd_ar augment_restrict [sh_ar_1, sh_ar_2, sh_ar_3] forbid [augment_conflictFree_iff, restrict_fold]

/-! ## Shadows for `augment_conflictFree_iff` -/

/-- NL: "a flow is a parameter intervention on the augmented model" — a
conflict-free `P` augmented by conflict-free new atoms is a conflict-free program. -/
theorem sh_ac_1 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M)
    (hP : ConflictFree P) (hQ : ConflictFree Q) : ConflictFree (augment P Q) := by
  intro t j
  rcases j with j | j'
  · rw [restrict_fold]; exact hP t j
  · rw [augment_fresh]; exact hQ t j'

/-- NL: "unchanged on the original targets" — conflict-freeness of the augmented
program restricts to `P`. -/
theorem sh_ac_2 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M)
    (h : ConflictFree (augment P Q)) : ConflictFree P := by
  intro t j
  rw [← restrict_fold P Q j t]
  exact h t (Sum.inl j)

/-- NL facet: … and to the new atoms. -/
theorem sh_ac_3 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M)
    (h : ConflictFree (augment P Q)) : ConflictFree Q := by
  intro t j'
  rw [← augment_fresh P Q j' t]
  exact h t (Sum.inr j')

/-- NL: "a flow is a parameter intervention" — adding one flow atom on a fresh
target is conflict-free exactly when `P` is. -/
theorem sh_ac_4 {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ]
    [DecidableEq T] [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M) :
    ConflictFree (augment P [⟨0, j', s, e⟩]) ↔ ConflictFree P :=
  ⟨sh_ac_2 P _, fun h => sh_ac_1 P _ h (conflictFree_singleton _)⟩

sa_check_shadow_free sh_ac_1 [augment_restrict, augment_conflictFree_iff, augmentFlow_conflictFree_iff]
sa_check_shadow_free sh_ac_2 [augment_restrict, augment_conflictFree_iff, augmentFlow_conflictFree_iff]
sa_check_shadow_free sh_ac_3 [augment_restrict, augment_conflictFree_iff, augmentFlow_conflictFree_iff]
sa_check_shadow_free sh_ac_4 [augment_restrict, augment_conflictFree_iff, augmentFlow_conflictFree_iff]

theorem fwd_ac_1
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree P → ConflictFree Q → ConflictFree (augment P Q) := by
  intro τ T T' M _ _ _ _ P Q hP hQ
  exact (hT P Q).mpr ⟨hP, hQ⟩

sa_check_fwd fwd_ac_1 augment_conflictFree_iff sh_ac_1
  forbid [augment_restrict, augmentFlow_conflictFree_iff, restrict_fold, sh_ac_2, sh_ac_3, sh_ac_4]

theorem fwd_ac_2
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) → ConflictFree P := by
  intro τ T T' M _ _ _ _ P Q h
  exact ((hT P Q).mp h).1

sa_check_fwd fwd_ac_2 augment_conflictFree_iff sh_ac_2
  forbid [augment_restrict, augmentFlow_conflictFree_iff, restrict_fold, sh_ac_1, sh_ac_3, sh_ac_4]

theorem fwd_ac_3
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) → ConflictFree Q := by
  intro τ T T' M _ _ _ _ P Q h
  exact ((hT P Q).mp h).2

sa_check_fwd fwd_ac_3 augment_conflictFree_iff sh_ac_3
  forbid [augment_restrict, augmentFlow_conflictFree_iff, restrict_fold, sh_ac_1, sh_ac_2, sh_ac_4]

theorem fwd_ac_4
    (hT : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M),
      ConflictFree (augment P [⟨0, j', s, e⟩]) ↔ ConflictFree P := by
  intro τ T T' M _ _ _ _ P j' s e
  rw [hT]
  exact ⟨fun h => h.1, fun h => ⟨h, conflictFree_singleton _⟩⟩

sa_check_fwd fwd_ac_4 augment_conflictFree_iff sh_ac_4
  forbid [augment_restrict, augmentFlow_conflictFree_iff, restrict_fold, sh_ac_1, sh_ac_2, sh_ac_3]

theorem bwd_ac
    (h₁ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree P → ConflictFree Q → ConflictFree (augment P Q))
    (h₂ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) → ConflictFree P)
    (h₃ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) → ConflictFree Q)
    (h₄ : ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (j' : T') (s : Support τ) (e : M),
      ConflictFree (augment P [⟨0, j', s, e⟩]) ↔ ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {T' : Type w} {M : Type x} [LinearOrder τ] [DecidableEq T]
      [DecidableEq T'] [PCM M] (P : Program τ T M) (Q : Program τ T' M),
      ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q := by
  intro τ T T' M _ _ _ _ P Q
  have _ := @h₄
  exact ⟨fun h => ⟨h₂ P Q h, h₃ P Q h⟩, fun h => h₁ P Q h.1 h.2⟩

sa_check_bwd bwd_ac augment_conflictFree_iff [sh_ac_1, sh_ac_2, sh_ac_3, sh_ac_4]
  forbid [augment_restrict, augmentFlow_conflictFree_iff, restrict_fold]

end CategoricalInterventionsProofs.SAPass.C22
