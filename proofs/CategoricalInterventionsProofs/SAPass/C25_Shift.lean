import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Shift

/-!
# SA-Pass claims 24 and 25 (shift and sequence)

Claim 24: **"Shift commutes with composition, preserves conflict-freeness, and
acts by translating the schedule."**
Targets: `shift_append`, `conflictFree_shift`, `apply_shift`.

Claim 25: **"Sequence inherits the laws of composition and shift."**
Targets: `seq_assoc`, `seq_nil_left`, `seq_nil_right`, `conflictFree_of_seq`,
`seq_disjoint_conflictFree`, `apply_seq`.

Reading notes.  "Preserves conflict-freeness" for an *invertible* operation
(`shift (-δ)` undoes `shift δ`) is read as preservation; reflection then
follows, so the backward checker for `conflictFree_shift` needs only the
preservation shadow (with `shift_add`/`shift_zero` as glue).  "Inherits the
laws" for `seq` is read as: associativity and units of `++`, factor
conflict-freeness (both ways under temporal separation), and the homomorphism
law of `apply_append` composed with the translation law of `apply_shift`.
-/

namespace CategoricalInterventionsProofs.SAPass.C25

open CategoricalInterventionsProofs

universe u v w x

/-! ## Claim 24: shadows for `shift_append` -/

/-- NL: "commutes with composition" — membership form. -/
theorem sh_sa_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (b : Atom τ T M) :
    b ∈ shift δ (P ++ Q) ↔ b ∈ shift δ P ∨ b ∈ shift δ Q := by
  simp only [shift, List.map_append, List.mem_append]

/-- NL: "commutes with composition" — position-wise. -/
theorem sh_sa_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (i : ℕ) :
    (shift δ (P ++ Q))[i]? = (shift δ P ++ shift δ Q)[i]? := by
  simp only [shift, List.map_append]

/-- NL: "commutes with composition" — the unit of composition is preserved. -/
theorem sh_sa_3 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (δ : τ) : shift δ ([] : Program τ T M) = [] := rfl

sa_check_shadow_free sh_sa_1 [shift_append, conflictFree_shift, apply_shift]
sa_check_shadow_free sh_sa_2 [shift_append, conflictFree_shift, apply_shift]
sa_check_shadow_free sh_sa_3 [shift_append, conflictFree_shift, apply_shift]

theorem fwd_sa_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M),
      shift δ (P ++ Q) = shift δ P ++ shift δ Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (b : Atom τ T M),
      b ∈ shift δ (P ++ Q) ↔ b ∈ shift δ P ∨ b ∈ shift δ Q := by
  intro τ T M _ _ _ δ P Q b
  rw [hT, List.mem_append]

sa_check_fwd fwd_sa_1 shift_append sh_sa_1 forbid [conflictFree_shift, apply_shift, sh_sa_2, sh_sa_3]

theorem fwd_sa_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M),
      shift δ (P ++ Q) = shift δ P ++ shift δ Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (i : ℕ),
      (shift δ (P ++ Q))[i]? = (shift δ P ++ shift δ Q)[i]? := by
  intro τ T M _ _ _ δ P Q i
  rw [hT]

sa_check_fwd fwd_sa_2 shift_append sh_sa_2 forbid [conflictFree_shift, apply_shift, sh_sa_1, sh_sa_3]

/-- Forward: `shift δ [] = shift δ [] ++ shift δ []` forces `shift δ [] = []`. -/
theorem fwd_sa_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M),
      shift δ (P ++ Q) = shift δ P ++ shift δ Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ), shift δ ([] : Program τ T M) = [] := by
  intro τ T M _ _ _ δ
  have := hT δ ([] : Program τ T M) []
  rw [List.nil_append] at this
  exact List.self_eq_append_right.mp this

sa_check_fwd fwd_sa_3 shift_append sh_sa_3 forbid [conflictFree_shift, apply_shift, shift_nil, sh_sa_1, sh_sa_2]

theorem bwd_sa
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (b : Atom τ T M),
      b ∈ shift δ (P ++ Q) ↔ b ∈ shift δ P ∨ b ∈ shift δ Q)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M) (i : ℕ),
      (shift δ (P ++ Q))[i]? = (shift δ P ++ shift δ Q)[i]?)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ), shift δ ([] : Program τ T M) = []) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ) (P Q : Program τ T M),
      shift δ (P ++ Q) = shift δ P ++ shift δ Q := by
  intro τ T M _ _ _ δ P Q
  have _ := @h₁
  have _ := @h₃
  exact List.ext_getElem? (h₂ δ P Q)

sa_check_bwd bwd_sa shift_append [sh_sa_1, sh_sa_2, sh_sa_3] forbid [conflictFree_shift, apply_shift]

/-! ## Claim 24: shadows for `conflictFree_shift` -/

/-- NL: "preserves conflict-freeness". -/
theorem sh_cs_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M)
    (h : ConflictFree P) : ConflictFree (shift δ P) := by
  intro t j
  rw [foldAt_shift]
  exact h _ j

/-- NL facet: a conflict-free pair stays conflict-free when both atoms are
shifted together. -/
theorem sh_cs_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (a b : Atom τ T M)
    (h : ConflictFree [a, b]) : ConflictFree [a.shift δ, b.shift δ] :=
  sh_cs_1 δ [a, b] h

/-- NL facet: shifting never *creates* conflict-freeness either (reflection;
follows from preservation by shifting back). -/
theorem sh_cs_3 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M)
    (h : ConflictFree (shift δ P)) : ConflictFree P := by
  have := sh_cs_1 (-δ) _ h
  rwa [shift_add, neg_add_cancel, shift_zero] at this

sa_check_shadow_free sh_cs_1 [shift_append, conflictFree_shift, apply_shift]
sa_check_shadow_free sh_cs_2 [shift_append, conflictFree_shift, apply_shift]
sa_check_shadow_free sh_cs_3 [shift_append, conflictFree_shift, apply_shift]

theorem fwd_cs_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) ↔ ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree P → ConflictFree (shift δ P) := by
  intro τ T M _ _ _ _ _ δ P h
  exact (hT δ P).mpr h

sa_check_fwd fwd_cs_1 conflictFree_shift sh_cs_1 forbid [shift_append, apply_shift, foldAt_shift, sh_cs_2, sh_cs_3]

theorem fwd_cs_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) ↔ ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (a b : Atom τ T M),
      ConflictFree [a, b] → ConflictFree [a.shift δ, b.shift δ] := by
  intro τ T M _ _ _ _ _ δ a b h
  exact (hT δ [a, b]).mpr h

sa_check_fwd fwd_cs_2 conflictFree_shift sh_cs_2 forbid [shift_append, apply_shift, foldAt_shift, sh_cs_1, sh_cs_3]

theorem fwd_cs_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) ↔ ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) → ConflictFree P := by
  intro τ T M _ _ _ _ _ δ P h
  exact (hT δ P).mp h

sa_check_fwd fwd_cs_3 conflictFree_shift sh_cs_3 forbid [shift_append, apply_shift, foldAt_shift, sh_cs_1, sh_cs_2]

/-- Backward: preservation alone suffices, since `shift (-δ)` undoes `shift δ`
(`shift_add`, `shift_zero` are glue about the definition). -/
theorem bwd_cs
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree P → ConflictFree (shift δ P))
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (a b : Atom τ T M),
      ConflictFree [a, b] → ConflictFree [a.shift δ, b.shift δ])
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) → ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (δ : τ) (P : Program τ T M),
      ConflictFree (shift δ P) ↔ ConflictFree P := by
  intro τ T M _ _ _ _ _ δ P
  have _ := @h₂
  have _ := @h₃
  refine ⟨fun h => ?_, h₁ δ P⟩
  have := h₁ (-δ) _ h
  rwa [shift_add, neg_add_cancel, shift_zero] at this

sa_check_bwd bwd_cs conflictFree_shift [sh_cs_1, sh_cs_2, sh_cs_3] forbid [shift_append, apply_shift, foldAt_shift]

/-! ## Claim 24: shadows for `apply_shift` -/

/-- NL: "acts by translating the schedule" — as an equality of schedules. -/
theorem sh_as_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V]
    (δ : τ) (P : Program τ T M) (θ : τ → T → V) :
    apply (shift δ P) θ = fun t => apply P (fun s => θ (s + δ)) (t - δ) := by
  funext t j
  simp only [apply, foldAt_shift, sub_add_cancel]

/-- NL facet: the shifted program is inert where the original was inert `δ`
earlier (locality translates). -/
theorem sh_as_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V]
    (δ : τ) (P : Program τ T M) (θ : τ → T → V) (t : τ)
    (h : ∀ a ∈ P, ¬ a.support.mem (t - δ)) : apply (shift δ P) θ t = θ t := by
  apply apply_local
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_shift_iff.mp hb
  rw [Atom.shift_support, Support.mem_shift]
  exact h a ha

/-- NL: "translating the schedule" — translating the baseline along with the
program translates the output. -/
theorem sh_as_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V]
    (δ : τ) (P : Program τ T M) (θ : τ → T → V) (t : τ) :
    apply (shift δ P) (fun s => θ (s - δ)) (t + δ) = apply P θ t := by
  funext j
  simp only [apply, foldAt_shift, add_sub_cancel_right]

sa_check_shadow_free sh_as_1 [shift_append, conflictFree_shift, apply_shift, apply_shift', apply_shift_translate]
sa_check_shadow_free sh_as_2 [shift_append, conflictFree_shift, apply_shift, apply_shift', apply_shift_translate]
sa_check_shadow_free sh_as_3 [shift_append, conflictFree_shift, apply_shift, apply_shift', apply_shift_translate]

theorem fwd_as_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ) (j : T),
      apply (shift δ P) θ t j = apply P (fun s j => θ (s + δ) j) (t - δ) j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V), apply (shift δ P) θ = fun t => apply P (fun s => θ (s + δ)) (t - δ) := by
  intro τ T M V _ _ _ _ _ _ δ P θ
  funext t j
  exact hT δ P θ t j

sa_check_fwd fwd_as_1 apply_shift sh_as_1
  forbid [shift_append, conflictFree_shift, apply_shift', apply_shift_translate, foldAt_shift, sh_as_2, sh_as_3]

theorem fwd_as_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ) (j : T),
      apply (shift δ P) θ t j = apply P (fun s j => θ (s + δ) j) (t - δ) j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ), (∀ a ∈ P, ¬ a.support.mem (t - δ)) →
      apply (shift δ P) θ t = θ t := by
  intro τ T M V _ _ _ _ _ _ δ P θ t h
  funext j
  rw [hT, apply_local h]
  simp only [sub_add_cancel]

sa_check_fwd fwd_as_2 apply_shift sh_as_2
  forbid [shift_append, conflictFree_shift, apply_shift', apply_shift_translate, foldAt_shift, sh_as_1, sh_as_3]

theorem fwd_as_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ) (j : T),
      apply (shift δ P) θ t j = apply P (fun s j => θ (s + δ) j) (t - δ) j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ),
      apply (shift δ P) (fun s => θ (s - δ)) (t + δ) = apply P θ t := by
  intro τ T M V _ _ _ _ _ _ δ P θ t
  funext j
  rw [hT]
  simp only [add_sub_cancel_right]

sa_check_fwd fwd_as_3 apply_shift sh_as_3
  forbid [shift_append, conflictFree_shift, apply_shift', apply_shift_translate, foldAt_shift, sh_as_1, sh_as_2]

/-- Backward: from the translation facet with the baseline `s ↦ θ (s + δ)`. -/
theorem bwd_as
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V), apply (shift δ P) θ = fun t => apply P (fun s => θ (s + δ)) (t - δ))
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ), (∀ a ∈ P, ¬ a.support.mem (t - δ)) →
      apply (shift δ P) θ t = θ t)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ),
      apply (shift δ P) (fun s => θ (s - δ)) (t + δ) = apply P θ t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (δ : τ) (P : Program τ T M)
      (θ : τ → T → V) (t : τ) (j : T),
      apply (shift δ P) θ t j = apply P (fun s j => θ (s + δ) j) (t - δ) j := by
  intro τ T M V _ _ _ _ _ _ δ P θ t j
  have _ := @h₁
  have _ := @h₂
  have := h₃ δ P (fun s => θ (s + δ)) (t - δ)
  simp only [sub_add_cancel] at this
  exact congrFun this j

sa_check_bwd bwd_as apply_shift [sh_as_1, sh_as_2, sh_as_3]
  forbid [shift_append, conflictFree_shift, apply_shift', apply_shift_translate, foldAt_shift]

/-! ## Claim 25: shadows for `seq_assoc` -/

/-- NL: "inherits associativity" — position-wise. -/
theorem sh_sq_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (i : ℕ) :
    (seq (seq P Q δ₁) R (δ₁ + δ₂))[i]? = (seq P (seq Q R δ₂) δ₁)[i]? := by
  simp only [seq, shift_append, shift_add, List.append_assoc]

/-- NL: "inherits associativity" — membership form. -/
theorem sh_sq_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (a : Atom τ T M) :
    a ∈ seq (seq P Q δ₁) R (δ₁ + δ₂) ↔ a ∈ seq P (seq Q R δ₂) δ₁ := by
  simp only [seq, shift_append, shift_add, List.append_assoc]

/-- NL: "inherits associativity" — at the level of folds. -/
theorem sh_sq_3 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q R : Program τ T M) (δ₁ δ₂ : τ)
    (j : T) (t : τ) :
    foldAt j (seq (seq P Q δ₁) R (δ₁ + δ₂)) t = foldAt j (seq P (seq Q R δ₂) δ₁) t := by
  simp only [seq, shift_append, shift_add, List.append_assoc]

sa_check_shadow_free sh_sq_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_sq_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_sq_3 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

theorem fwd_sq_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ),
      seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (i : ℕ),
      (seq (seq P Q δ₁) R (δ₁ + δ₂))[i]? = (seq P (seq Q R δ₂) δ₁)[i]? := by
  intro τ T M _ _ _ P Q R δ₁ δ₂ i
  rw [hT]

sa_check_fwd fwd_sq_1 seq_assoc sh_sq_1
  forbid [seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sq_2, sh_sq_3]

theorem fwd_sq_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ),
      seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (a : Atom τ T M),
      a ∈ seq (seq P Q δ₁) R (δ₁ + δ₂) ↔ a ∈ seq P (seq Q R δ₂) δ₁ := by
  intro τ T M _ _ _ P Q R δ₁ δ₂ a
  rw [hT]

sa_check_fwd fwd_sq_2 seq_assoc sh_sq_2
  forbid [seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sq_1, sh_sq_3]

theorem fwd_sq_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ),
      seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q R : Program τ T M) (δ₁ δ₂ : τ)
      (j : T) (t : τ),
      foldAt j (seq (seq P Q δ₁) R (δ₁ + δ₂)) t = foldAt j (seq P (seq Q R δ₂) δ₁) t := by
  intro τ T M _ _ _ _ _ P Q R δ₁ δ₂ j t
  rw [hT]

sa_check_fwd fwd_sq_3 seq_assoc sh_sq_3
  forbid [seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sq_1, sh_sq_2]

theorem bwd_sq
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (i : ℕ),
      (seq (seq P Q δ₁) R (δ₁ + δ₂))[i]? = (seq P (seq Q R δ₂) δ₁)[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ) (a : Atom τ T M),
      a ∈ seq (seq P Q δ₁) R (δ₁ + δ₂) ↔ a ∈ seq P (seq Q R δ₂) δ₁)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q R : Program τ T M) (δ₁ δ₂ : τ)
      (j : T) (t : τ),
      foldAt j (seq (seq P Q δ₁) R (δ₁ + δ₂)) t = foldAt j (seq P (seq Q R δ₂) δ₁) t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P Q R : Program τ T M) (δ₁ δ₂ : τ),
      seq (seq P Q δ₁) R (δ₁ + δ₂) = seq P (seq Q R δ₂) δ₁ := by
  intro τ T M _ _ _ P Q R δ₁ δ₂
  have _ := @h₂
  have _ := @h₃
  exact List.ext_getElem? (h₁ P Q R δ₁ δ₂)

sa_check_bwd bwd_sq seq_assoc [sh_sq_1, sh_sq_2, sh_sq_3]
  forbid [seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

/-! ## Claim 25: shadows for `seq_nil_left` and `seq_nil_right` -/

/-- NL: "inherits the units" — the empty first factor leaves the delayed second
factor, position-wise. -/
theorem sh_sl_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ) (i : ℕ) :
    (seq [] Q δ)[i]? = (shift δ Q)[i]? := rfl

/-- NL facet: the empty sequence. -/
theorem sh_sl_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (δ : τ) : seq ([] : Program τ T M) [] δ = [] := rfl

/-- NL: "inherits the units" — the empty second factor is dropped, position-wise. -/
theorem sh_sr_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ) (i : ℕ) :
    (seq P [] δ)[i]? = P[i]? := by
  simp only [seq, shift_nil, List.append_nil]

/-- NL facet: the empty second factor does not change the action. -/
theorem sh_sr_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V]
    (P : Program τ T M) (δ : τ) (θ : τ → T → V) : apply (seq P [] δ) θ = apply P θ := by
  simp only [seq, shift_nil, List.append_nil]

sa_check_shadow_free sh_sl_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_sl_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_sr_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_sr_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

theorem fwd_sl_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ), seq [] Q δ = shift δ Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ) (i : ℕ),
      (seq [] Q δ)[i]? = (shift δ Q)[i]? := by
  intro τ T M _ _ _ Q δ i
  rw [hT]

sa_check_fwd fwd_sl_1 seq_nil_left sh_sl_1
  forbid [seq_assoc, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sl_2]

theorem fwd_sl_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ), seq [] Q δ = shift δ Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ), seq ([] : Program τ T M) [] δ = [] := by
  intro τ T M _ _ _ δ
  rw [hT]
  rfl

sa_check_fwd fwd_sl_2 seq_nil_left sh_sl_2
  forbid [seq_assoc, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sl_1]

theorem bwd_sl
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ) (i : ℕ),
      (seq [] Q δ)[i]? = (shift δ Q)[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (δ : τ), seq ([] : Program τ T M) [] δ = []) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (Q : Program τ T M) (δ : τ), seq [] Q δ = shift δ Q := by
  intro τ T M _ _ _ Q δ
  have _ := @h₂
  exact List.ext_getElem? (h₁ Q δ)

sa_check_bwd bwd_sl seq_nil_left [sh_sl_1, sh_sl_2]
  forbid [seq_assoc, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

theorem fwd_sr_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ), seq P [] δ = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ) (i : ℕ), (seq P [] δ)[i]? = P[i]? := by
  intro τ T M _ _ _ P δ i
  rw [hT]

sa_check_fwd fwd_sr_1 seq_nil_right sh_sr_1
  forbid [seq_assoc, seq_nil_left, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sr_2]

theorem fwd_sr_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ), seq P [] δ = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (δ : τ)
      (θ : τ → T → V), apply (seq P [] δ) θ = apply P θ := by
  intro τ T M V _ _ _ _ _ _ P δ θ
  rw [hT]

sa_check_fwd fwd_sr_2 seq_nil_right sh_sr_2
  forbid [seq_assoc, seq_nil_left, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, sh_sr_1]

theorem bwd_sr
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ) (i : ℕ), (seq P [] δ)[i]? = P[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (δ : τ)
      (θ : τ → T → V), apply (seq P [] δ) θ = apply P θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] (P : Program τ T M) (δ : τ), seq P [] δ = P := by
  intro τ T M _ _ _ P δ
  have _ := @h₂
  exact List.ext_getElem? (h₁ P δ)

sa_check_bwd bwd_sr seq_nil_right [sh_sr_1, sh_sr_2]
  forbid [seq_assoc, seq_nil_left, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

/-! ## Claim 25: shadows for `conflictFree_of_seq` -/

/-- NL: "inherits factor conflict-freeness" — the first factor. -/
theorem sh_cq_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ)
    (h : ConflictFree (seq P Q δ)) : ConflictFree P :=
  conflictFree_append_left h

/-- NL: "inherits factor conflict-freeness" — the second factor, unshifted. -/
theorem sh_cq_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ)
    (h : ConflictFree (seq P Q δ)) : ConflictFree Q :=
  (conflictFree_shift δ Q).mp (conflictFree_append_right h)

/-- NL facet: the second factor as it appears in the sequence (shifted). -/
theorem sh_cq_3 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ)
    (h : ConflictFree (seq P Q δ)) : ConflictFree (shift δ Q) :=
  conflictFree_append_right h

sa_check_shadow_free sh_cq_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append]
sa_check_shadow_free sh_cq_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append]
sa_check_shadow_free sh_cq_3 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append]

theorem fwd_cq_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree P := by
  intro τ T M _ _ _ _ _ P Q δ h
  exact (hT h).1

sa_check_fwd fwd_cq_1 conflictFree_of_seq sh_cq_1
  forbid [seq_assoc, seq_nil_left, seq_nil_right, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append,
    conflictFree_append_left, conflictFree_append_right, sh_cq_2, sh_cq_3]

theorem fwd_cq_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree Q := by
  intro τ T M _ _ _ _ _ P Q δ h
  exact (hT h).2

sa_check_fwd fwd_cq_2 conflictFree_of_seq sh_cq_2
  forbid [seq_assoc, seq_nil_left, seq_nil_right, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append,
    conflictFree_append_left, conflictFree_append_right, sh_cq_1, sh_cq_3]

theorem fwd_cq_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree (shift δ Q) := by
  intro τ T M _ _ _ _ _ P Q δ h
  exact (conflictFree_shift δ Q).mpr (hT h).2

sa_check_fwd fwd_cq_3 conflictFree_of_seq sh_cq_3
  forbid [seq_assoc, seq_nil_left, seq_nil_right, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append,
    conflictFree_append_left, conflictFree_append_right, sh_cq_1, sh_cq_2]

theorem bwd_cq
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree P)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree Q)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      ConflictFree (seq P Q δ) → ConflictFree (shift δ Q)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q := by
  intro τ T M _ _ _ _ _ P Q δ h
  have _ := @h₃
  exact ⟨h₁ P Q δ h, h₂ P Q δ h⟩

sa_check_bwd bwd_cq conflictFree_of_seq [sh_cq_1, sh_cq_2, sh_cq_3]
  forbid [seq_assoc, seq_nil_left, seq_nil_right, seq_disjoint_conflictFree, apply_seq, conflictFree_of_append,
    conflictFree_append_left, conflictFree_append_right]

/-! ## Claim 25: shadows for `seq_disjoint_conflictFree` -/

/-- The separation hypothesis of the target, named for readability. -/
def Separated {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] (P Q : Program τ T M) (δ : τ) : Prop :=
  ∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t → a.target ≠ b.target

/-- NL: "inherits conflict-freeness from its factors" — under temporal
separation, conflict-free factors give a conflict-free sequence.  Proved from
`foldAt_append` and the unit folds, without the development's separated-append
lemma. -/
theorem sh_sd_1 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ)
    (hsep : Separated P Q δ) (hP : ConflictFree P) (hQ : ConflictFree Q) :
    ConflictFree (seq P Q δ) := by
  intro t j
  rw [seq, foldAt_append]
  by_cases hex : ∃ a ∈ P, a.support.mem t ∧ a.target = j
  · obtain ⟨a, ha, hta, hj⟩ := hex
    have hQ1 : foldAt j (shift δ Q) t = some one := by
      apply foldAt_eq_one_of_none
      intro b hb htb e
      obtain ⟨b₀, hb₀, rfl⟩ := mem_shift_iff.mp hb
      exact hsep a ha b₀ hb₀ t hta htb (hj.trans e.symm)
    rw [hQ1]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hP t j)
    simp [hx, mul_one]
  · push Not at hex
    have hP1 : foldAt j P t = some one :=
      foldAt_eq_one_of_none j P t (fun a ha hta => hex a ha hta)
    rw [hP1, foldAt_shift]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hQ (t - δ) j)
    simp [hy, one_mul]

/-- NL: the intended use — `Q` delayed so that it starts (at or) after every
atom of `P` has ended: the sequence is conflict-free iff both factors are. -/
theorem sh_sd_2 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ b₀ : τ)
    (hP : ∀ a ∈ P, ∀ t, a.support.mem t → t < b₀)
    (hQ : ∀ q ∈ Q, ∀ t, (q.shift δ).support.mem t → b₀ ≤ t) :
    ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q := by
  have hsep : Separated P Q δ := fun a ha q hq t hta htq =>
    absurd (lt_of_lt_of_le (hP a ha t hta) (hQ q hq t htq)) (lt_irrefl t)
  exact ⟨fun h => ⟨conflictFree_append_left h,
    (conflictFree_shift δ Q).mp (conflictFree_append_right h)⟩,
    fun ⟨h₁, h₂⟩ => sh_sd_1 P Q δ hsep h₁ h₂⟩

/-- NL facet: under separation, the factors of a conflict-free sequence are
conflict-free (the direction that holds even without separation). -/
theorem sh_sd_3 {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
    [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ)
    (_hsep : Separated P Q δ) (h : ConflictFree (seq P Q δ)) :
    ConflictFree P ∧ ConflictFree Q :=
  ⟨conflictFree_append_left h, (conflictFree_shift δ Q).mp (conflictFree_append_right h)⟩

sa_check_shadow_free sh_sd_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_append_iff_of_separated]
sa_check_shadow_free sh_sd_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_append_iff_of_separated]
sa_check_shadow_free sh_sd_3 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq, conflictFree_append_iff_of_separated]

theorem fwd_sd_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      (∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t → a.target ≠ b.target) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      Separated P Q δ → ConflictFree P → ConflictFree Q → ConflictFree (seq P Q δ) := by
  intro τ T M _ _ _ _ _ P Q δ hsep hP hQ
  exact (hT hsep).mpr ⟨hP, hQ⟩

sa_check_fwd fwd_sd_1 seq_disjoint_conflictFree sh_sd_1
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, apply_seq,
    conflictFree_append_iff_of_separated, sh_sd_2, sh_sd_3]

theorem fwd_sd_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      (∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t → a.target ≠ b.target) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ b₀ : τ),
      (∀ a ∈ P, ∀ t, a.support.mem t → t < b₀) →
      (∀ q ∈ Q, ∀ t, (q.shift δ).support.mem t → b₀ ≤ t) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q) := by
  intro τ T M _ _ _ _ _ P Q δ b₀ hP hQ
  apply hT
  intro a ha q hq t hta htq
  exact absurd (lt_of_lt_of_le (hP a ha t hta) (hQ q hq t htq)) (lt_irrefl t)

sa_check_fwd fwd_sd_2 seq_disjoint_conflictFree sh_sd_2
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, apply_seq,
    conflictFree_append_iff_of_separated, sh_sd_1, sh_sd_3]

theorem fwd_sd_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      (∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t → a.target ≠ b.target) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      Separated P Q δ → ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q := by
  intro τ T M _ _ _ _ _ P Q δ hsep h
  exact (hT hsep).mp h

sa_check_fwd fwd_sd_3 seq_disjoint_conflictFree sh_sd_3
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, apply_seq,
    conflictFree_append_iff_of_separated, sh_sd_1, sh_sd_2]

theorem bwd_sd
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      Separated P Q δ → ConflictFree P → ConflictFree Q → ConflictFree (seq P Q δ))
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ b₀ : τ),
      (∀ a ∈ P, ∀ t, a.support.mem t → t < b₀) →
      (∀ q ∈ Q, ∀ t, (q.shift δ).support.mem t → b₀ ≤ t) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q))
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] (P Q : Program τ T M) (δ : τ),
      Separated P Q δ → ConflictFree (seq P Q δ) → ConflictFree P ∧ ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] {P Q : Program τ T M} {δ : τ},
      (∀ a ∈ P, ∀ b ∈ Q, ∀ t, a.support.mem t → (b.shift δ).support.mem t → a.target ≠ b.target) →
      (ConflictFree (seq P Q δ) ↔ ConflictFree P ∧ ConflictFree Q) := by
  intro τ T M _ _ _ _ _ P Q δ hsep
  have _ := @h₂
  exact ⟨h₃ P Q δ hsep, fun ⟨hP, hQ⟩ => h₁ P Q δ hsep hP hQ⟩

sa_check_bwd bwd_sd seq_disjoint_conflictFree [sh_sd_1, sh_sd_2, sh_sd_3]
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, apply_seq,
    conflictFree_append_iff_of_separated]

/-! ## Claim 25: shadows for `apply_seq` -/

/-- NL: "inherits the homomorphism law of composition and the translation law of
shift" — `P`, then `Q` acting at translated times on `P`'s output. -/
theorem sh_aq_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V]
    (P Q : Program τ T M) (δ : τ) (h : ConflictFree (seq P Q δ)) (θ : τ → T → V) (t : τ) (j : T) :
    apply (seq P Q δ) θ t j = apply Q (fun s j => apply P θ (s + δ) j) (t - δ) j := by
  rw [seq, apply_append h, apply_shift]

/-- NL facet: the other order of the homomorphism law also holds for a sequence. -/
theorem sh_aq_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ]
    [LinearOrder τ] [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V]
    (P Q : Program τ T M) (δ : τ) (h : ConflictFree (seq P Q δ)) (θ : τ → T → V) :
    apply (seq P Q δ) θ = apply P (apply (shift δ Q) θ) :=
  apply_append' h θ

sa_check_shadow_free sh_aq_1 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]
sa_check_shadow_free sh_aq_2 [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree, apply_seq]

theorem fwd_aq_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] {P Q : Program τ T M}
      {δ : τ}, ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V),
      apply (seq P Q δ) θ = apply (shift δ Q) (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M)
      (δ : τ), ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V) (t : τ) (j : T),
      apply (seq P Q δ) θ t j = apply Q (fun s j => apply P θ (s + δ) j) (t - δ) j := by
  intro τ T M V _ _ _ _ _ _ P Q δ h θ t j
  rw [hT h, apply_shift]

sa_check_fwd fwd_aq_1 apply_seq sh_aq_1
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree,
    apply_append, apply_append', sh_aq_2]

/-- Forward: the other order, via `apply_comm` and the target applied to the
swapped sequence `seq (shift δ Q) P 0`. -/
theorem fwd_aq_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] {P Q : Program τ T M}
      {δ : τ}, ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V),
      apply (seq P Q δ) θ = apply (shift δ Q) (apply P θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M)
      (δ : τ), ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V),
      apply (seq P Q δ) θ = apply P (apply (shift δ Q) θ) := by
  intro τ T M V _ _ _ _ _ _ P Q δ h θ
  have hcf : ConflictFree (seq (shift δ Q) P 0) := by
    intro t j
    rw [seq, shift_zero, foldAt_perm List.perm_append_comm]
    exact h t j
  have e := hT hcf θ
  rw [seq, shift_zero] at e
  rw [seq, apply_comm]
  exact e

sa_check_fwd fwd_aq_2 apply_seq sh_aq_2
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree,
    apply_append, apply_append', sh_aq_1]

theorem bwd_aq
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M)
      (δ : τ), ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V) (t : τ) (j : T),
      apply (seq P Q δ) θ t j = apply Q (fun s j => apply P θ (s + δ) j) (t - δ) j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] (P Q : Program τ T M)
      (δ : τ), ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V),
      apply (seq P Q δ) θ = apply P (apply (shift δ Q) θ)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [AddCommGroup τ] [LinearOrder τ]
      [IsOrderedAddMonoid τ] [DecidableEq T] [PCM M] [PCMAction M V] {P Q : Program τ T M}
      {δ : τ}, ConflictFree (seq P Q δ) → ∀ (θ : τ → T → V),
      apply (seq P Q δ) θ = apply (shift δ Q) (apply P θ) := by
  intro τ T M V _ _ _ _ _ _ P Q δ h θ
  have _ := @h₂
  funext t j
  rw [h₁ P Q δ h θ t j, apply_shift]

sa_check_bwd bwd_aq apply_seq [sh_aq_1, sh_aq_2]
  forbid [seq_assoc, seq_nil_left, seq_nil_right, conflictFree_of_seq, seq_disjoint_conflictFree,
    apply_append, apply_append']

end CategoricalInterventionsProofs.SAPass.C25
