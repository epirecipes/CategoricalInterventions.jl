import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.Common

/-!
# SA-Pass claim 5

NL claim: **"Factors of a conflict-free composite are conflict-free."**
Targets: `conflictFree_append_left`, `conflictFree_append_right`.

The sentence has no side condition and none is needed: the composite fold is
`foldP.bind (fun a => foldQ.bind (mul a))`, which is defined only if both
factor folds are.  The theorems, however, assume `PCMPairwise M` (they are
proved through `conflictFree_sublist`).
-/

namespace CategoricalInterventionsProofs.SAPass.C05

open CategoricalInterventionsProofs

universe u v w

/-! ## Shadows for `conflictFree_append_left` -/

/-- NL: "the left factor of a conflict-free composite is conflict-free" — for
every PCM (no pairwise hypothesis), with the composite written `P ⊕ᵢ Q`. -/
theorem sh_facL_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (P Q : Program τ T M) (h : ConflictFree (P ⊕ᵢ Q)) : ConflictFree P :=
  conflictFree_of_append_left h

/-- NL facet: every *prefix* of a conflict-free program is conflict-free (a
prefix is the left factor of the composite `take n ++ drop n`). -/
theorem sh_facL_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    [PCMPairwise M] (P : Program τ T M) (n : ℕ) (h : ConflictFree P) :
    ConflictFree (P.take n) := by
  rw [← List.take_append_drop n P] at h
  exact conflictFree_of_append_left h

sa_check_shadow_free sh_facL_1 [conflictFree_append_left, conflictFree_append_right, conflictFree_sublist]
sa_check_shadow_free sh_facL_2 [conflictFree_append_left, conflictFree_append_right, conflictFree_sublist]

/- `fwd_facL_1` (conflictFree_append_left ⇒ sh_facL_1) is OMITTED: the shadow is
stated for every PCM, and the target cannot be instantiated without a
`PCMPairwise M` instance.  The theorem carries an unnecessary hypothesis.
See SA-PASS.md. -/

theorem fwd_facL_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P Q : Program τ T M}, ConflictFree (P ++ Q) → ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M) (n : ℕ), ConflictFree P → ConflictFree (P.take n) := by
  intro τ T M _ _ _ _ P n h
  rw [← List.take_append_drop n P] at h
  exact hT h

sa_check_fwd fwd_facL_2 conflictFree_append_left sh_facL_2
  forbid [conflictFree_append_right, conflictFree_sublist, sh_facL_1, conflictFree_of_append_left]

theorem bwd_facL
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P Q : Program τ T M), ConflictFree (P ⊕ᵢ Q) → ConflictFree P)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M) (n : ℕ), ConflictFree P → ConflictFree (P.take n)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P Q : Program τ T M}, ConflictFree (P ++ Q) → ConflictFree P := by
  intro τ T M _ _ _ _ P Q h
  have _ := @h₂
  exact h₁ P Q h

sa_check_bwd bwd_facL conflictFree_append_left [sh_facL_1, sh_facL_2]
  forbid [conflictFree_append_right, conflictFree_sublist, conflictFree_of_append_left]

/-! ## Shadows for `conflictFree_append_right` -/

/-- NL: "the right factor of a conflict-free composite is conflict-free" — for
every PCM (no pairwise hypothesis). -/
theorem sh_facR_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (P Q : Program τ T M) (h : ConflictFree (P ⊕ᵢ Q)) : ConflictFree Q :=
  conflictFree_of_append_right h

/-- NL facet: every *suffix* of a conflict-free program is conflict-free. -/
theorem sh_facR_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    [PCMPairwise M] (P : Program τ T M) (n : ℕ) (h : ConflictFree P) :
    ConflictFree (P.drop n) := by
  rw [← List.take_append_drop n P] at h
  exact conflictFree_of_append_right h

sa_check_shadow_free sh_facR_1 [conflictFree_append_left, conflictFree_append_right, conflictFree_sublist]
sa_check_shadow_free sh_facR_2 [conflictFree_append_left, conflictFree_append_right, conflictFree_sublist]

/- `fwd_facR_1` OMITTED for the same reason as `fwd_facL_1`. -/

theorem fwd_facR_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P Q : Program τ T M}, ConflictFree (P ++ Q) → ConflictFree Q) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M) (n : ℕ), ConflictFree P → ConflictFree (P.drop n) := by
  intro τ T M _ _ _ _ P n h
  rw [← List.take_append_drop n P] at h
  exact hT h

sa_check_fwd fwd_facR_2 conflictFree_append_right sh_facR_2
  forbid [conflictFree_append_left, conflictFree_sublist, sh_facR_1, conflictFree_of_append_right]

theorem bwd_facR
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (P Q : Program τ T M), ConflictFree (P ⊕ᵢ Q) → ConflictFree Q)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M) (n : ℕ), ConflictFree P → ConflictFree (P.drop n)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P Q : Program τ T M}, ConflictFree (P ++ Q) → ConflictFree Q := by
  intro τ T M _ _ _ _ P Q h
  have _ := @h₂
  exact h₁ P Q h

sa_check_bwd bwd_facR conflictFree_append_right [sh_facR_1, sh_facR_2]
  forbid [conflictFree_append_left, conflictFree_sublist, conflictFree_of_append_right]

end CategoricalInterventionsProofs.SAPass.C05
