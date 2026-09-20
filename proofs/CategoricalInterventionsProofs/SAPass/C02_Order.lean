import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Semantics
import Mathlib.Data.List.Rotate

/-!
# SA-Pass claim 2

NL claim: **"Under a partial commutative monoid, the order of atoms never matters."**
Targets: `fold_perm`, `foldAt_perm`, `apply_comm`.
-/

namespace CategoricalInterventionsProofs.SAPass.C02

open CategoricalInterventionsProofs

universe u v w x

/-! ## Shadows for `fold_perm` (order of effects in a fold) -/

/-- NL: "the order never matters".  Facet: swapping two adjacent effects does not
change the fold (the generator of all permutations). -/
theorem sh_fold_1 {M : Type u} [PCM M] (a b : M) (l : List M) :
    foldList (a :: b :: l) = foldList (b :: a :: l) := by
  simp only [foldList_cons]
  cases foldList l with
  | none => rfl
  | some c =>
    simp only [Option.bind_some]
    have h1 := mul_assoc a b c
    have h2 := mul_assoc b a c
    rw [mul_comm a b] at h1
    rw [← h1, ← h2]

/-- NL: "the order never matters".  Facet: reversing the list does not change the fold. -/
theorem sh_fold_2 {M : Type u} [PCM M] (l : List M) : foldList l.reverse = foldList l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, foldList_append, ih, foldList_singleton, foldList_cons]
    cases foldList l with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      exact mul_comm x a

/-- NL: "the order never matters".  Facet: the fold is a function of the
*multiset* of effects. -/
theorem sh_fold_3 {M : Type u} [PCM M] (l l' : List M)
    (h : (l : Multiset M) = (l' : Multiset M)) : foldList l = foldList l' := by
  have hp : l.Perm l' := Multiset.coe_eq_coe.mp h
  clear h
  induction hp with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => exact sh_fold_1 y x l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

sa_check_shadow_free sh_fold_1 [fold_perm, foldAt_perm, apply_comm]
sa_check_shadow_free sh_fold_2 [fold_perm, foldAt_perm, apply_comm]
sa_check_shadow_free sh_fold_3 [fold_perm, foldAt_perm, apply_comm]

theorem fwd_fold_1
    (hT : ∀ {M : Type u} [PCM M] {l l' : List M}, l.Perm l' → foldList l = foldList l') :
    ∀ {M : Type u} [PCM M] (a b : M) (l : List M),
      foldList (a :: b :: l) = foldList (b :: a :: l) := by
  intro M _ a b l
  exact hT (List.Perm.swap b a l)

sa_check_fwd fwd_fold_1 fold_perm sh_fold_1 forbid [foldAt_perm, apply_comm, sh_fold_2, sh_fold_3]

theorem fwd_fold_2
    (hT : ∀ {M : Type u} [PCM M] {l l' : List M}, l.Perm l' → foldList l = foldList l') :
    ∀ {M : Type u} [PCM M] (l : List M), foldList l.reverse = foldList l := by
  intro M _ l
  exact hT (List.reverse_perm l)

sa_check_fwd fwd_fold_2 fold_perm sh_fold_2 forbid [foldAt_perm, apply_comm, sh_fold_1, sh_fold_3]

theorem fwd_fold_3
    (hT : ∀ {M : Type u} [PCM M] {l l' : List M}, l.Perm l' → foldList l = foldList l') :
    ∀ {M : Type u} [PCM M] (l l' : List M),
      (l : Multiset M) = (l' : Multiset M) → foldList l = foldList l' := by
  intro M _ l l' h
  exact hT (Multiset.coe_eq_coe.mp h)

sa_check_fwd fwd_fold_3 fold_perm sh_fold_3 forbid [foldAt_perm, apply_comm, sh_fold_1, sh_fold_2]

/-- Backward: adjacent swaps generate all permutations (`List.Perm` induction). -/
theorem bwd_fold
    (h₁ : ∀ {M : Type u} [PCM M] (a b : M) (l : List M),
      foldList (a :: b :: l) = foldList (b :: a :: l))
    (h₂ : ∀ {M : Type u} [PCM M] (l : List M), foldList l.reverse = foldList l)
    (h₃ : ∀ {M : Type u} [PCM M] (l l' : List M),
      (l : Multiset M) = (l' : Multiset M) → foldList l = foldList l') :
    ∀ {M : Type u} [PCM M] {l l' : List M}, l.Perm l' → foldList l = foldList l' := by
  intro M _ l l' h
  have _ := @h₂
  have _ := @h₃
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => exact h₁ y x l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

sa_check_bwd bwd_fold fold_perm [sh_fold_1, sh_fold_2, sh_fold_3] forbid [foldAt_perm, apply_comm]

/-! ## Shadows for `foldAt_perm` (order of atoms in a program) -/

/-- NL: "the order of atoms never matters".  Facet: swapping two adjacent atoms
changes no fold. -/
theorem sh_foldAt_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] (a b : Atom τ T M) (P : Program τ T M) (j : T) (t : τ) :
    foldAt j (a :: b :: P) t = foldAt j (b :: a :: P) t := by
  simp only [foldAt_cons]
  split_ifs <;> try rfl
  cases foldAt j P t with
  | none => rfl
  | some c =>
    simp only [Option.bind_some]
    have h1 := mul_assoc a.effect b.effect c
    have h2 := mul_assoc b.effect a.effect c
    rw [mul_comm a.effect b.effect] at h1
    rw [← h1, ← h2]

/-- NL: "the order of atoms never matters".  Facet: reversing a program changes no fold. -/
theorem sh_foldAt_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] (P : Program τ T M) (j : T) (t : τ) :
    foldAt j P.reverse t = foldAt j P t := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    rw [List.reverse_cons, foldAt_append, ih, foldAt_cons, foldAt_cons, foldAt_nil]
    by_cases h : a.support.mem t ∧ a.target = j
    · rw [if_pos h, if_pos h, Option.bind_some, mul_one]
      cases foldAt j P t with
      | none => rfl
      | some x =>
        simp only [Option.bind_some]
        exact mul_comm x a.effect
    · rw [if_neg h, if_neg h]
      cases foldAt j P t with
      | none => rfl
      | some x => simp only [Option.bind_some, mul_one]

/-- NL: "the order of atoms never matters".  Facet: every fold is a function of
the *multiset* of atoms. -/
theorem sh_foldAt_3 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] (P Q : Program τ T M) (h : (P : Multiset (Atom τ T M)) = Q) (j : T) (t : τ) :
    foldAt j P t = foldAt j Q t := by
  have hp : P.Perm Q := Multiset.coe_eq_coe.mp h
  clear h
  induction hp with
  | nil => rfl
  | cons x _ ih => rw [foldAt_cons, foldAt_cons, ih]
  | swap x y l => exact sh_foldAt_1 y x l j t
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

sa_check_shadow_free sh_foldAt_1 [fold_perm, foldAt_perm, apply_comm]
sa_check_shadow_free sh_foldAt_2 [fold_perm, foldAt_perm, apply_comm]
sa_check_shadow_free sh_foldAt_3 [fold_perm, foldAt_perm, apply_comm]

theorem fwd_foldAt_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {P Q : Program τ T M}, P.Perm Q → ∀ (j : T) (t : τ), foldAt j P t = foldAt j Q t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (P : Program τ T M) (j : T) (t : τ),
      foldAt j (a :: b :: P) t = foldAt j (b :: a :: P) t := by
  intro τ T M _ _ _ a b P j t
  exact hT (List.Perm.swap b a P) j t

sa_check_fwd fwd_foldAt_1 foldAt_perm sh_foldAt_1 forbid [fold_perm, apply_comm, sh_foldAt_2, sh_foldAt_3]

theorem fwd_foldAt_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {P Q : Program τ T M}, P.Perm Q → ∀ (j : T) (t : τ), foldAt j P t = foldAt j Q t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P : Program τ T M) (j : T) (t : τ), foldAt j P.reverse t = foldAt j P t := by
  intro τ T M _ _ _ P j t
  exact hT (List.reverse_perm P) j t

sa_check_fwd fwd_foldAt_2 foldAt_perm sh_foldAt_2 forbid [fold_perm, apply_comm, sh_foldAt_1, sh_foldAt_3]

theorem fwd_foldAt_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {P Q : Program τ T M}, P.Perm Q → ∀ (j : T) (t : τ), foldAt j P t = foldAt j Q t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P Q : Program τ T M), (P : Multiset (Atom τ T M)) = Q → ∀ (j : T) (t : τ),
      foldAt j P t = foldAt j Q t := by
  intro τ T M _ _ _ P Q h j t
  exact hT (Multiset.coe_eq_coe.mp h) j t

sa_check_fwd fwd_foldAt_3 foldAt_perm sh_foldAt_3 forbid [fold_perm, apply_comm, sh_foldAt_1, sh_foldAt_2]

theorem bwd_foldAt
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (P : Program τ T M) (j : T) (t : τ),
      foldAt j (a :: b :: P) t = foldAt j (b :: a :: P) t)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P : Program τ T M) (j : T) (t : τ), foldAt j P.reverse t = foldAt j P t)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P Q : Program τ T M), (P : Multiset (Atom τ T M)) = Q → ∀ (j : T) (t : τ),
      foldAt j P t = foldAt j Q t) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {P Q : Program τ T M}, P.Perm Q → ∀ (j : T) (t : τ), foldAt j P t = foldAt j Q t := by
  intro τ T M _ _ _ P Q h j t
  have _ := @h₂
  have _ := @h₃
  induction h with
  | nil => rfl
  | cons x _ ih => rw [foldAt_cons, foldAt_cons, ih]
  | swap x y l => exact h₁ y x l j t
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

sa_check_bwd bwd_foldAt foldAt_perm [sh_foldAt_1, sh_foldAt_2, sh_foldAt_3] forbid [fold_perm, apply_comm]

/-! ## Shadows for `apply_comm` (order of atoms for the action on schedules) -/

/-- NL: "the order of atoms never matters" — for the action on schedules: any
two programs that are permutations of each other act identically. -/
theorem sh_apply_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] (P Q : Program τ T M) (h : P.Perm Q)
    (θ : τ → T → V) : apply P θ = apply Q θ := by
  funext t j
  simp only [apply]
  rw [sh_foldAt_3 P Q (Multiset.coe_eq_coe.mpr h) j t]

/-- NL: "the order of atoms never matters".  Facet: rotating a program (moving a
prefix to the end) does not change its action. -/
theorem sh_apply_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] (P : Program τ T M) (n : ℕ) (θ : τ → T → V) :
    apply (P.rotate n) θ = apply P θ :=
  sh_apply_1 _ _ (List.rotate_perm P n) θ

sa_check_shadow_free sh_apply_1 [fold_perm, foldAt_perm, apply_comm]
sa_check_shadow_free sh_apply_2 [fold_perm, foldAt_perm, apply_comm]

/- `fwd_apply_1` (apply_comm ⇒ sh_apply_1) is OMITTED: `apply_comm` only swaps
the two blocks of a composite, i.e. it is invariance under *rotations* of the
atom list, which does not generate all permutations (a rotation-invariant but
not permutation-invariant function of a list exists, e.g. "b follows a
cyclically").  The claim "the order of atoms never matters" is strictly
stronger than the theorem.  See SA-PASS.md. -/

theorem fwd_apply_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P Q : Program τ T M) (θ : τ → T → V),
      apply (P ++ Q) θ = apply (Q ++ P) θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M) (n : ℕ) (θ : τ → T → V),
      apply (P.rotate n) θ = apply P θ := by
  intro τ T M V _ _ _ _ P n θ
  rw [List.rotate_eq_drop_append_take_mod, hT, List.take_append_drop]

sa_check_fwd fwd_apply_2 apply_comm sh_apply_2 forbid [fold_perm, foldAt_perm, sh_apply_1]

/-- Backward: block swap is a rotation by the length of the first block. -/
theorem bwd_apply
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P Q : Program τ T M), P.Perm Q → ∀ (θ : τ → T → V),
      apply P θ = apply Q θ)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P : Program τ T M) (n : ℕ) (θ : τ → T → V),
      apply (P.rotate n) θ = apply P θ) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] (P Q : Program τ T M) (θ : τ → T → V),
      apply (P ++ Q) θ = apply (Q ++ P) θ := by
  intro τ T M V _ _ _ _ P Q θ
  have _ := @h₁
  rw [← List.rotate_append_length_eq P Q, h₂]

sa_check_bwd bwd_apply apply_comm [sh_apply_1, sh_apply_2] forbid [fold_perm, foldAt_perm]

end CategoricalInterventionsProofs.SAPass.C02
