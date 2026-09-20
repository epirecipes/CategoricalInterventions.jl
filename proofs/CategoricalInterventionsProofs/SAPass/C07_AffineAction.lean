import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.PCM

/-!
# SA-Pass claim 7

NL claim: **"Under set-then-scale the absolute value is applied first, then the
relative product."**
Targets: `affine_action`, `affine_act_mul_of_relative`.
-/

namespace CategoricalInterventionsProofs.SAPass.C07

open CategoricalInterventionsProofs

universe u v

/-- Glue: the absolute part of a defined product is the absolute of whichever
factor has one. -/
theorem abs_of_mul {V : Type u} {M : Type v} [PCM M] {x y z : Affine V M}
    (h : mul x y = some z) : z.abs = x.abs.or y.abs := by
  obtain ⟨xa, ma⟩ := x
  obtain ⟨xb, mb⟩ := y
  obtain ⟨xc, mc⟩ := z
  simp only [Affine.pcm_mul, Affine.mul_mk] at h
  cases xa <;> cases xb <;>
    simp only [absMul_none_left, absMul_none_right, absMul_some_some, Option.bind_some,
      Option.bind_none, Option.map_eq_some_iff, Affine.mk.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨m, hm, rfl, rfl⟩ := h
    rfl

/-! ## Shadows for `affine_action` -/

/-- NL: "the absolute value is applied first, then the relative".  Facet: with
an absolute `a` present, the current value is discarded and the relative effect
acts on `a`. -/
theorem sh_aact_1 {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m : M) (v : V) :
    act (⟨some a, m⟩ : Affine V M) v = act m a := rfl

/-- NL facet: with no absolute, the relative effect acts on the current value. -/
theorem sh_aact_2 {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m : M) (v : V) :
    act (⟨none, m⟩ : Affine V M) v = act m v := rfl

/-- NL facet: a defined product whose first factor carries an absolute `a` acts
by its relative part on `a` (the absolute survives composition and is still
applied first). -/
theorem sh_aact_3 {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M)
    (a : V) (v : V) (h : mul x y = some z) (hx : x.abs = some a) : act z v = act z.rel a := by
  have hz := abs_of_mul h
  rw [hx, Option.some_or] at hz
  rw [Affine.act_def, hz]
  rfl

sa_check_shadow_free sh_aact_1 [affine_action, affine_act_mul_of_relative]
sa_check_shadow_free sh_aact_2 [affine_action, affine_act_mul_of_relative]
sa_check_shadow_free sh_aact_3 [affine_action, affine_act_mul_of_relative]

theorem fwd_aact_1
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (v : V),
      act (one : Affine V M) v = v ∧ (mul x y = some z → act z v = act z.rel ((x.abs.or y.abs).getD v)) ∧
      act x v = act x.rel (x.abs.getD v)) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m : M) (v : V),
      act (⟨some a, m⟩ : Affine V M) v = act m a := by
  intro V M _ _ a m v
  exact (hT ⟨some a, m⟩ ⟨some a, m⟩ ⟨some a, m⟩ v).2.2

sa_check_fwd fwd_aact_1 affine_action sh_aact_1
  forbid [affine_act_mul_of_relative, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_aact_2, sh_aact_3]

theorem fwd_aact_2
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (v : V),
      act (one : Affine V M) v = v ∧ (mul x y = some z → act z v = act z.rel ((x.abs.or y.abs).getD v)) ∧
      act x v = act x.rel (x.abs.getD v)) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m : M) (v : V),
      act (⟨none, m⟩ : Affine V M) v = act m v := by
  intro V M _ _ m v
  exact (hT ⟨none, m⟩ ⟨none, m⟩ ⟨none, m⟩ v).2.2

sa_check_fwd fwd_aact_2 affine_action sh_aact_2
  forbid [affine_act_mul_of_relative, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_aact_1, sh_aact_3]

theorem fwd_aact_3
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (v : V),
      act (one : Affine V M) v = v ∧ (mul x y = some z → act z v = act z.rel ((x.abs.or y.abs).getD v)) ∧
      act x v = act x.rel (x.abs.getD v)) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (a : V) (v : V),
      mul x y = some z → x.abs = some a → act z v = act z.rel a := by
  intro V M _ _ x y z a v h hx
  rw [(hT x y z v).2.1 h, hx, Option.some_or]
  rfl

sa_check_fwd fwd_aact_3 affine_action sh_aact_3
  forbid [affine_act_mul_of_relative, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_aact_1, sh_aact_2]

theorem bwd_aact
    (h₁ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m : M) (v : V),
      act (⟨some a, m⟩ : Affine V M) v = act m a)
    (h₂ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m : M) (v : V),
      act (⟨none, m⟩ : Affine V M) v = act m v)
    (h₃ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (a : V) (v : V),
      mul x y = some z → x.abs = some a → act z v = act z.rel a) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (x y z : Affine V M) (v : V),
      act (one : Affine V M) v = v ∧ (mul x y = some z → act z v = act z.rel ((x.abs.or y.abs).getD v)) ∧
      act x v = act x.rel (x.abs.getD v) := by
  intro V M _ _ x y z v
  -- the third conjunct, for an arbitrary element, from the two constructor cases
  have third : ∀ w : Affine V M, act w v = act w.rel (w.abs.getD v) := by
    intro w
    obtain ⟨wa, mw⟩ := w
    cases wa with
    | none => exact h₂ mw v
    | some a => exact h₁ a mw v
  refine ⟨?_, ?_, third x⟩
  · rw [Affine.pcm_one, h₂]
    exact act_one v
  · intro h
    cases hx : x.abs with
    | some a =>
      rw [h₃ x y z a v h hx, Option.some_or]
      rfl
    | none =>
      rw [third z, abs_of_mul h, hx, Option.none_or]

sa_check_bwd bwd_aact affine_action [sh_aact_1, sh_aact_2, sh_aact_3]
  forbid [affine_act_mul_of_relative, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none]

/-! ## Shadows for `affine_act_mul_of_relative` -/

/-- NL: "absolute first, then the relative product".  Facet: setting to `a` and
scaling by `m`, then scaling by a purely relative `m'`, is setting to `a` and
scaling by the product `m·m'`. -/
theorem sh_rel_1 {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m m' mm' : M)
    (h : mul m m' = some mm') (v : V) :
    act (⟨none, m'⟩ : Affine V M) (act (⟨some a, m⟩ : Affine V M) v) = act (⟨some a, mm'⟩ : Affine V M) v := by
  simp only [Affine.act_def, Option.getD_none, Option.getD_some]
  exact (act_mul' a h).symm

/-- NL facet: two purely relative effects applied in sequence act as their product. -/
theorem sh_rel_2 {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m m' mm' : M)
    (h : mul m m' = some mm') (v : V) :
    act (⟨none, m'⟩ : Affine V M) (act (⟨none, m⟩ : Affine V M) v) = act (⟨none, mm'⟩ : Affine V M) v := by
  simp only [Affine.act_def, Option.getD_none]
  exact (act_mul' v h).symm

sa_check_shadow_free sh_rel_1 [affine_action, affine_act_mul_of_relative]
sa_check_shadow_free sh_rel_2 [affine_action, affine_act_mul_of_relative]

theorem fwd_rel_1
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] {x y z : Affine V M} (v : V),
      y.abs = none → mul x y = some z → act z v = act y (act x v)) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m m' mm' : M),
      mul m m' = some mm' → ∀ (v : V),
      act (⟨none, m'⟩ : Affine V M) (act (⟨some a, m⟩ : Affine V M) v) = act (⟨some a, mm'⟩ : Affine V M) v := by
  intro V M _ _ a m m' mm' h v
  have hmul : mul (⟨some a, m⟩ : Affine V M) ⟨none, m'⟩ = some ⟨some a, mm'⟩ := by
    simp [Affine.mul_mk, h]
  exact (hT v rfl hmul).symm

sa_check_fwd fwd_rel_1 affine_act_mul_of_relative sh_rel_1
  forbid [affine_action, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_rel_2]

theorem fwd_rel_2
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] {x y z : Affine V M} (v : V),
      y.abs = none → mul x y = some z → act z v = act y (act x v)) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m m' mm' : M),
      mul m m' = some mm' → ∀ (v : V),
      act (⟨none, m'⟩ : Affine V M) (act (⟨none, m⟩ : Affine V M) v) = act (⟨none, mm'⟩ : Affine V M) v := by
  intro V M _ _ m m' mm' h v
  have hmul : mul (⟨none, m⟩ : Affine V M) ⟨none, m'⟩ = some ⟨none, mm'⟩ := by
    simp [Affine.mul_mk, h]
  exact (hT v rfl hmul).symm

sa_check_fwd fwd_rel_2 affine_act_mul_of_relative sh_rel_2
  forbid [affine_action, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none, sh_rel_1]

theorem bwd_rel
    (h₁ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (a : V) (m m' mm' : M),
      mul m m' = some mm' → ∀ (v : V),
      act (⟨none, m'⟩ : Affine V M) (act (⟨some a, m⟩ : Affine V M) v) = act (⟨some a, mm'⟩ : Affine V M) v)
    (h₂ : ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] (m m' mm' : M),
      mul m m' = some mm' → ∀ (v : V),
      act (⟨none, m'⟩ : Affine V M) (act (⟨none, m⟩ : Affine V M) v) = act (⟨none, mm'⟩ : Affine V M) v) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMAction M V] {x y z : Affine V M} (v : V),
      y.abs = none → mul x y = some z → act z v = act y (act x v) := by
  intro V M _ _ x y z v hy h
  obtain ⟨xa, m⟩ := x
  obtain ⟨yb, m'⟩ := y
  obtain ⟨zc, mz⟩ := z
  simp only at hy
  subst hy
  simp only [Affine.pcm_mul, Affine.mul_mk, absMul_none_right, Option.bind_some,
    Option.map_eq_some_iff, Affine.mk.injEq] at h
  obtain ⟨mm', hm, rfl, rfl⟩ := h
  cases xa with
  | none => exact (h₂ m m' mm' hm v).symm
  | some a => exact (h₁ a m m' mm' hm v).symm

sa_check_bwd bwd_rel affine_act_mul_of_relative [sh_rel_1, sh_rel_2]
  forbid [affine_action, affine_act_mul_of_relative', Affine.act_eq_of_mul,
    Affine.act_one', Affine.act_mul_of_relative, Affine.act_mul_of_abs_none]

end CategoricalInterventionsProofs.SAPass.C07
