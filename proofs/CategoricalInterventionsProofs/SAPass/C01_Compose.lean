import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Program

/-!
# SA-Pass claim 1

NL claim: **"Programs compose associatively with the empty program as identity."**
Targets: `compose_assoc`, `compose_nil_left`, `compose_nil_right`.
-/

namespace CategoricalInterventionsProofs.SAPass.C01

open CategoricalInterventionsProofs

universe u v w

/-! ## Shadows for `compose_assoc` -/

/-- NL: "programs compose associatively".  Facet: the two bracketings of a
triple composite agree atom-by-atom at every position. -/
theorem sh_assoc_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ]
    (P Q R : Program τ T M) (i : ℕ) :
    ((P ⊕ᵢ Q) ⊕ᵢ R)[i]? = (P ⊕ᵢ (Q ⊕ᵢ R))[i]? := by
  simp [compose, List.append_assoc]

/-- NL: "programs compose associatively".  Facet: `compose` is an associative
binary operation in the sense of the `Std.Associative` typeclass. -/
theorem sh_assoc_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] :
    Std.Associative (α := Program τ T M) compose :=
  ⟨fun P Q R => List.append_assoc P Q R⟩

sa_check_shadow_free sh_assoc_1 [compose_assoc, compose_nil_left, compose_nil_right]
sa_check_shadow_free sh_assoc_2 [compose_assoc, compose_nil_left, compose_nil_right]

/-! ## Checkers for `compose_assoc` -/

theorem fwd_assoc_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q R : Program τ T M),
      (P ⊕ᵢ Q) ⊕ᵢ R = P ⊕ᵢ (Q ⊕ᵢ R)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q R : Program τ T M) (i : ℕ),
      ((P ⊕ᵢ Q) ⊕ᵢ R)[i]? = (P ⊕ᵢ (Q ⊕ᵢ R))[i]? := by
  intro τ T M _ P Q R i
  rw [hT]

sa_check_fwd fwd_assoc_1 compose_assoc sh_assoc_1 forbid [compose_nil_left, compose_nil_right, sh_assoc_2]

theorem fwd_assoc_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q R : Program τ T M),
      (P ⊕ᵢ Q) ⊕ᵢ R = P ⊕ᵢ (Q ⊕ᵢ R)) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.Associative (α := Program τ T M) compose := by
  intro τ T M _
  exact ⟨fun P Q R => hT P Q R⟩

sa_check_fwd fwd_assoc_2 compose_assoc sh_assoc_2 forbid [compose_nil_left, compose_nil_right, sh_assoc_1]

theorem bwd_assoc
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q R : Program τ T M) (i : ℕ),
      ((P ⊕ᵢ Q) ⊕ᵢ R)[i]? = (P ⊕ᵢ (Q ⊕ᵢ R))[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.Associative (α := Program τ T M) compose) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P Q R : Program τ T M),
      (P ⊕ᵢ Q) ⊕ᵢ R = P ⊕ᵢ (Q ⊕ᵢ R) := by
  intro τ T M _ P Q R
  have _ := @h₂
  exact List.ext_getElem? (h₁ P Q R)

sa_check_bwd bwd_assoc compose_assoc [sh_assoc_1, sh_assoc_2] forbid [compose_nil_left, compose_nil_right]

/-! ## Shadows for `compose_nil_left` -/

/-- NL: "the empty program is an identity" (on the left).  Facet: position-wise,
prepending the empty program changes no atom. -/
theorem sh_nilL_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ]
    (P : Program τ T M) (i : ℕ) : (([] : Program τ T M) ⊕ᵢ P)[i]? = P[i]? := rfl

/-- NL: "the empty program is an identity" (on the left).  Facet: `[]` is a
lawful left identity of `compose` in the `Std` sense. -/
theorem sh_nilL_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] :
    Std.LawfulLeftIdentity (α := Program τ T M) compose [] :=
  { left_id := fun P => List.nil_append P }

sa_check_shadow_free sh_nilL_1 [compose_assoc, compose_nil_left, compose_nil_right]
sa_check_shadow_free sh_nilL_2 [compose_assoc, compose_nil_left, compose_nil_right]

theorem fwd_nilL_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      ([] : Program τ T M) ⊕ᵢ P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (i : ℕ),
      (([] : Program τ T M) ⊕ᵢ P)[i]? = P[i]? := by
  intro τ T M _ P i
  rw [hT]

sa_check_fwd fwd_nilL_1 compose_nil_left sh_nilL_1 forbid [compose_assoc, compose_nil_right, sh_nilL_2]

theorem fwd_nilL_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      ([] : Program τ T M) ⊕ᵢ P = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.LawfulLeftIdentity (α := Program τ T M) compose [] := by
  intro τ T M _
  exact { left_id := fun P => hT P }

sa_check_fwd fwd_nilL_2 compose_nil_left sh_nilL_2 forbid [compose_assoc, compose_nil_right, sh_nilL_1]

theorem bwd_nilL
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (i : ℕ),
      (([] : Program τ T M) ⊕ᵢ P)[i]? = P[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.LawfulLeftIdentity (α := Program τ T M) compose []) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      ([] : Program τ T M) ⊕ᵢ P = P := by
  intro τ T M _ P
  have _ := @h₁
  exact h₂.left_id P

sa_check_bwd bwd_nilL compose_nil_left [sh_nilL_1, sh_nilL_2] forbid [compose_assoc, compose_nil_right]

/-! ## Shadows for `compose_nil_right` -/

/-- NL: "the empty program is an identity" (on the right).  Facet: position-wise,
appending the empty program changes no atom. -/
theorem sh_nilR_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ]
    (P : Program τ T M) (i : ℕ) : (P ⊕ᵢ ([] : Program τ T M))[i]? = P[i]? := by
  simp [compose]

/-- NL: "the empty program is an identity" (on the right).  Facet: `[]` is a
lawful right identity of `compose` in the `Std` sense. -/
theorem sh_nilR_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] :
    Std.LawfulRightIdentity (α := Program τ T M) compose [] :=
  { right_id := fun P => List.append_nil P }

sa_check_shadow_free sh_nilR_1 [compose_assoc, compose_nil_left, compose_nil_right]
sa_check_shadow_free sh_nilR_2 [compose_assoc, compose_nil_left, compose_nil_right]

theorem fwd_nilR_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      P ⊕ᵢ ([] : Program τ T M) = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (i : ℕ),
      (P ⊕ᵢ ([] : Program τ T M))[i]? = P[i]? := by
  intro τ T M _ P i
  rw [hT]

sa_check_fwd fwd_nilR_1 compose_nil_right sh_nilR_1 forbid [compose_assoc, compose_nil_left, sh_nilR_2]

theorem fwd_nilR_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      P ⊕ᵢ ([] : Program τ T M) = P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.LawfulRightIdentity (α := Program τ T M) compose [] := by
  intro τ T M _
  exact { right_id := fun P => hT P }

sa_check_fwd fwd_nilR_2 compose_nil_right sh_nilR_2 forbid [compose_assoc, compose_nil_left, sh_nilR_1]

theorem bwd_nilR
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M) (i : ℕ),
      (P ⊕ᵢ ([] : Program τ T M))[i]? = P[i]?)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ],
      Std.LawfulRightIdentity (α := Program τ T M) compose []) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] (P : Program τ T M),
      P ⊕ᵢ ([] : Program τ T M) = P := by
  intro τ T M _ P
  have _ := @h₂
  exact List.ext_getElem? (h₁ P)

sa_check_bwd bwd_nilR compose_nil_right [sh_nilR_1, sh_nilR_2] forbid [compose_assoc, compose_nil_left]

end CategoricalInterventionsProofs.SAPass.C01
