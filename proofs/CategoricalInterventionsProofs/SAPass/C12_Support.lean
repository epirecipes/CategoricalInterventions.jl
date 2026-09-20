import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Support

/-!
# SA-Pass claim 12

NL claim: **"Supports are order-convex."**
Target: `support_ordConnected`.
-/

namespace CategoricalInterventionsProofs.SAPass.C12

open CategoricalInterventionsProofs

universe u

/-- NL: "order-convex" — pointwise: a time between two times of a support is in
the support. -/
theorem sh_oc_1 {τ : Type u} [LinearOrder τ] (S : Support τ) (x y z : τ) (hx : S.mem x)
    (hz : S.mem z) (hxy : x ≤ y) (hyz : y ≤ z) : S.mem y := by
  cases S with
  | span s => exact ⟨le_trans hx.1 hxy, lt_of_le_of_lt hyz hz.2⟩
  | instant i =>
    simp only [Support.mem_instant] at *
    subst hx
    subst hz
    exact le_antisymm hyz hxy

/-- NL: "order-convex" — interval form: the closed interval between two times
of a support lies in the support. -/
theorem sh_oc_2 {τ : Type u} [LinearOrder τ] (S : Support τ) (x z : τ) (hx : S.mem x)
    (hz : S.mem z) : Set.Icc x z ⊆ S.memSet := by
  intro y ⟨hxy, hyz⟩
  exact sh_oc_1 S x y z hx hz hxy hyz

/-- NL facet: in particular spans are order-convex (stated on `Span.mem`). -/
theorem sh_oc_3 {τ : Type u} [LinearOrder τ] (s : Span τ) (x y z : τ) (hx : s.mem x)
    (hz : s.mem z) (hxy : x ≤ y) (hyz : y ≤ z) : s.mem y :=
  sh_oc_1 (Support.span s) x y z hx hz hxy hyz

sa_check_shadow_free sh_oc_1 [support_ordConnected]
sa_check_shadow_free sh_oc_2 [support_ordConnected]
sa_check_shadow_free sh_oc_3 [support_ordConnected]

theorem fwd_oc_1
    (hT : ∀ {τ : Type u} [LinearOrder τ] (S : Support τ), S.memSet.OrdConnected) :
    ∀ {τ : Type u} [LinearOrder τ] (S : Support τ) (x y z : τ), S.mem x → S.mem z →
      x ≤ y → y ≤ z → S.mem y := by
  intro τ _ S x y z hx hz hxy hyz
  exact (hT S).out hx hz ⟨hxy, hyz⟩

sa_check_fwd fwd_oc_1 support_ordConnected sh_oc_1 forbid [sh_oc_2, sh_oc_3]

theorem fwd_oc_2
    (hT : ∀ {τ : Type u} [LinearOrder τ] (S : Support τ), S.memSet.OrdConnected) :
    ∀ {τ : Type u} [LinearOrder τ] (S : Support τ) (x z : τ), S.mem x → S.mem z →
      Set.Icc x z ⊆ S.memSet := by
  intro τ _ S x z hx hz
  exact (hT S).out hx hz

sa_check_fwd fwd_oc_2 support_ordConnected sh_oc_2 forbid [sh_oc_1, sh_oc_3]

theorem fwd_oc_3
    (hT : ∀ {τ : Type u} [LinearOrder τ] (S : Support τ), S.memSet.OrdConnected) :
    ∀ {τ : Type u} [LinearOrder τ] (s : Span τ) (x y z : τ), s.mem x → s.mem z →
      x ≤ y → y ≤ z → s.mem y := by
  intro τ _ s x y z hx hz hxy hyz
  exact (hT (Support.span s)).out hx hz ⟨hxy, hyz⟩

sa_check_fwd fwd_oc_3 support_ordConnected sh_oc_3 forbid [sh_oc_1, sh_oc_2]

theorem bwd_oc
    (h₁ : ∀ {τ : Type u} [LinearOrder τ] (S : Support τ) (x y z : τ), S.mem x → S.mem z →
      x ≤ y → y ≤ z → S.mem y)
    (h₂ : ∀ {τ : Type u} [LinearOrder τ] (S : Support τ) (x z : τ), S.mem x → S.mem z →
      Set.Icc x z ⊆ S.memSet)
    (h₃ : ∀ {τ : Type u} [LinearOrder τ] (s : Span τ) (x y z : τ), s.mem x → s.mem z →
      x ≤ y → y ≤ z → s.mem y) :
    ∀ {τ : Type u} [LinearOrder τ] (S : Support τ), S.memSet.OrdConnected := by
  intro τ _ S
  have _ := @h₂
  have _ := @h₃
  exact ⟨fun x hx z hz y hy => h₁ S x y z hx hz hy.1 hy.2⟩

sa_check_bwd bwd_oc support_ordConnected [sh_oc_1, sh_oc_2, sh_oc_3]

end CategoricalInterventionsProofs.SAPass.C12
