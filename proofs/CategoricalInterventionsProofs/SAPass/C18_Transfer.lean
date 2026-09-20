import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Lowering

/-!
# SA-Pass claim 18

NL claim: **"Transfers conserve the total."**
Target: `transfer_preserves_sum`.
-/

namespace CategoricalInterventionsProofs.SAPass.C18

open CategoricalInterventionsProofs Finset

universe u v

/-- Glue (a re-proof of conservation from the definition, used by the shadows). -/
theorem sum_transfer {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T]
    (x : T → G) (src dst : T) (n : G) : ∑ j, transfer x src dst n j = ∑ j, x j := by
  simp [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- NL: "conserve the total" — the net change summed over compartments is zero. -/
theorem sh_tr_1 {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T]
    (x : T → G) (src dst : T) (n : G) : ∑ j, (transfer x src dst n j - x j) = 0 := by
  rw [Finset.sum_sub_distrib, sum_transfer, sub_self]

/-- NL facet: two successive transfers conserve the total. -/
theorem sh_tr_2 {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T]
    (x : T → G) (s d s' d' : T) (n n' : G) :
    ∑ j, transfer (transfer x s d n) s' d' n' j = ∑ j, x j := by
  rw [sum_transfer, sum_transfer]

/-- NL facet: any finite sequence of transfers conserves the total. -/
theorem sh_tr_3 {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T]
    (x : T → G) (moves : List (T × T × G)) :
    ∑ j, (moves.foldl (fun y (m : T × T × G) => transfer y m.1 m.2.1 m.2.2) x) j = ∑ j, x j := by
  induction moves generalizing x with
  | nil => rfl
  | cons m moves ih =>
    simp only [List.foldl_cons]
    rw [ih, sum_transfer]

sa_check_shadow_free sh_tr_1 [transfer_preserves_sum]
sa_check_shadow_free sh_tr_2 [transfer_preserves_sum]
sa_check_shadow_free sh_tr_3 [transfer_preserves_sum]

theorem fwd_tr_1
    (hT : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, transfer x src dst n j = ∑ j, x j) :
    ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, (transfer x src dst n j - x j) = 0 := by
  intro T G _ _ _ x src dst n
  rw [Finset.sum_sub_distrib, hT, sub_self]

sa_check_fwd fwd_tr_1 transfer_preserves_sum sh_tr_1 forbid [sum_transfer, sh_tr_2, sh_tr_3]

theorem fwd_tr_2
    (hT : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, transfer x src dst n j = ∑ j, x j) :
    ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (s d s' d' : T) (n n' : G), ∑ j, transfer (transfer x s d n) s' d' n' j = ∑ j, x j := by
  intro T G _ _ _ x s d s' d' n n'
  rw [hT, hT]

sa_check_fwd fwd_tr_2 transfer_preserves_sum sh_tr_2 forbid [sum_transfer, sh_tr_1, sh_tr_3]

theorem fwd_tr_3
    (hT : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, transfer x src dst n j = ∑ j, x j) :
    ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (moves : List (T × T × G)),
      ∑ j, (moves.foldl (fun y (m : T × T × G) => transfer y m.1 m.2.1 m.2.2) x) j = ∑ j, x j := by
  intro T G _ _ _ x moves
  induction moves generalizing x with
  | nil => rfl
  | cons m moves ih =>
    simp only [List.foldl_cons]
    rw [ih, hT]

sa_check_fwd fwd_tr_3 transfer_preserves_sum sh_tr_3 forbid [sum_transfer, sh_tr_1, sh_tr_2]

theorem bwd_tr
    (h₁ : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, (transfer x src dst n j - x j) = 0)
    (h₂ : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (s d s' d' : T) (n n' : G), ∑ j, transfer (transfer x s d n) s' d' n' j = ∑ j, x j)
    (h₃ : ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (moves : List (T × T × G)),
      ∑ j, (moves.foldl (fun y (m : T × T × G) => transfer y m.1 m.2.1 m.2.2) x) j = ∑ j, x j) :
    ∀ {T : Type u} {G : Type v} [AddCommGroup G] [Fintype T] [DecidableEq T] (x : T → G)
      (src dst : T) (n : G), ∑ j, transfer x src dst n j = ∑ j, x j := by
  intro T G _ _ _ x src dst n
  have _ := @h₂
  have _ := @h₃
  have := h₁ x src dst n
  rwa [Finset.sum_sub_distrib, sub_eq_zero] at this

sa_check_bwd bwd_tr transfer_preserves_sum [sh_tr_1, sh_tr_2, sh_tr_3] forbid [sum_transfer]

end CategoricalInterventionsProofs.SAPass.C18
