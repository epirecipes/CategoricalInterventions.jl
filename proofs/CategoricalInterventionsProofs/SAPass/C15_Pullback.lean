import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Semantics

/-!
# SA-Pass claim 15

NL claim: **"Applying a program commutes with restricting or resampling the schedule."**
Targets: `apply_pullback`, `grid_preimage_span`, `apply_discrete_eq`.
-/

namespace CategoricalInterventionsProofs.SAPass.C15

open CategoricalInterventionsProofs

universe u v w x y

/-! ## Shadows for `apply_pullback` -/

/-- NL: "commutes with reparametrising the schedule" — pointwise naturality
along any map `r`. -/
theorem sh_pb_1 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M)
    (θ : τ → T → V) (t' : τ') (j : T) :
    apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j := by
  simp only [apply, gapply, foldAt, effectsAt, active, pullback]
  congr 2
  symm
  apply gapply_filter_map
  · intro a _
    exact decide_eq_decide.mpr Iff.rfl
  · intro a _
    rfl
  · intro a
    rfl

/-- NL: "restricting the schedule" — naturality along an injective
reparametrisation (an embedding of a sub-timeline). -/
theorem sh_pb_2 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (_hr : Function.Injective r)
    (P : Program τ T M) (θ : τ → T → V) (t' : τ') (j : T) :
    apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j :=
  sh_pb_1 r P θ t' j

/-- NL: "resampling the schedule" — resampling twice (along `r` then `r'`) is
resampling once along the composite. -/
theorem sh_pb_3 {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ]
    [DecidableEq T] [PCM M] [HasAct M V] {τ' τ'' : Type y} (r : τ' → τ) (r' : τ'' → τ')
    (P : Program τ T M) (θ : τ → T → V) (t'' : τ'') (j : T) :
    apply P θ (r (r' t'')) j =
      gapply (pullback (r ∘ r') P) (fun t'' => θ (r (r' t''))) t'' j :=
  sh_pb_1 (r ∘ r') P θ t'' j

sa_check_shadow_free sh_pb_1 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_pb_2 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_pb_3 [apply_pullback, grid_preimage_span, apply_discrete_eq]

theorem fwd_pb_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V),
      (fun t' => apply P θ (r t')) = gapply (pullback r P) fun t' => θ (r t')) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V)
      (t' : τ') (j : T), apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j := by
  intro τ T M V _ _ _ _ τ' r P θ t' j
  exact congrFun (congrFun (hT r P θ) t') j

sa_check_fwd fwd_pb_1 apply_pullback sh_pb_1 forbid [grid_preimage_span, apply_discrete_eq, gapply_filter_map, sh_pb_2, sh_pb_3]

theorem fwd_pb_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V),
      (fun t' => apply P θ (r t')) = gapply (pullback r P) fun t' => θ (r t')) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ), Function.Injective r →
      ∀ (P : Program τ T M) (θ : τ → T → V) (t' : τ') (j : T),
      apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j := by
  intro τ T M V _ _ _ _ τ' r _ P θ t' j
  exact congrFun (congrFun (hT r P θ) t') j

sa_check_fwd fwd_pb_2 apply_pullback sh_pb_2 forbid [grid_preimage_span, apply_discrete_eq, gapply_filter_map, sh_pb_1, sh_pb_3]

theorem fwd_pb_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V),
      (fun t' => apply P θ (r t')) = gapply (pullback r P) fun t' => θ (r t')) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' τ'' : Type y} (r : τ' → τ) (r' : τ'' → τ')
      (P : Program τ T M) (θ : τ → T → V) (t'' : τ'') (j : T),
      apply P θ (r (r' t'')) j =
        gapply (pullback (r ∘ r') P) (fun t'' => θ (r (r' t''))) t'' j := by
  intro τ T M V _ _ _ _ τ' τ'' r r' P θ t'' j
  exact congrFun (congrFun (hT (r ∘ r') P θ) t'') j

sa_check_fwd fwd_pb_3 apply_pullback sh_pb_3 forbid [grid_preimage_span, apply_discrete_eq, gapply_filter_map, sh_pb_1, sh_pb_2]

theorem bwd_pb
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V)
      (t' : τ') (j : T), apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ), Function.Injective r →
      ∀ (P : Program τ T M) (θ : τ → T → V) (t' : τ') (j : T),
      apply P θ (r t') j = gapply (pullback r P) (fun t' => θ (r t')) t' j)
    (h₃ : ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' τ'' : Type y} (r : τ' → τ) (r' : τ'' → τ')
      (P : Program τ T M) (θ : τ → T → V) (t'' : τ'') (j : T),
      apply P θ (r (r' t'')) j =
        gapply (pullback (r ∘ r') P) (fun t'' => θ (r (r' t''))) t'' j) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} {V : Type x} [LinearOrder τ] [DecidableEq T]
      [PCM M] [HasAct M V] {τ' : Type y} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V),
      (fun t' => apply P θ (r t')) = gapply (pullback r P) fun t' => θ (r t') := by
  intro τ T M V _ _ _ _ τ' r P θ
  have _ := @h₂
  have _ := @h₃
  funext t' j
  exact h₁ r P θ t' j

sa_check_bwd bwd_pb apply_pullback [sh_pb_1, sh_pb_2, sh_pb_3] forbid [grid_preimage_span, apply_discrete_eq, gapply_filter_map]

/-! ## Shadows for `grid_preimage_span` -/

/-- NL: "resampling" — a grid point lies in the span `[a, b)` iff its index lies
in the integer span of the ceilings. -/
theorem sh_gp_1 {t₀ Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) (k : ℤ) :
    (a ≤ grid t₀ Δ k ∧ grid t₀ Δ k < b) ↔ (⌈(a - t₀) / Δ⌉ ≤ k ∧ k < ⌈(b - t₀) / Δ⌉) := by
  simp only [grid, Int.ceil_le, Int.lt_ceil, div_le_iff₀ hΔ, lt_div_iff₀ hΔ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- NL facet: the preimage of a span under the grid is an integer span. -/
theorem sh_gp_2 {t₀ Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) :
    ∃ m n : ℤ, grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico m n := by
  refine ⟨⌈(a - t₀) / Δ⌉, ⌈(b - t₀) / Δ⌉, ?_⟩
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico]
  exact sh_gp_1 hΔ a b k

/-- NL facet (unit grid): the preimage of `[a, b)` under `k ↦ k` is `[⌈a⌉, ⌈b⌉)`. -/
theorem sh_gp_3 (a b : ℝ) : grid 0 1 ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico]
  have := sh_gp_1 (t₀ := 0) (Δ := 1) one_pos a b k
  simpa using this

sa_check_shadow_free sh_gp_1 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_gp_2 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_gp_3 [apply_pullback, grid_preimage_span, apply_discrete_eq]

theorem fwd_gp_1
    (hT : ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ),
      grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico ⌈(a - t₀) / Δ⌉ ⌈(b - t₀) / Δ⌉) :
    ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ) (k : ℤ),
      (a ≤ grid t₀ Δ k ∧ grid t₀ Δ k < b) ↔ (⌈(a - t₀) / Δ⌉ ≤ k ∧ k < ⌈(b - t₀) / Δ⌉) := by
  intro t₀ Δ hΔ a b k
  have := Set.ext_iff.mp (hT (t₀ := t₀) hΔ a b) k
  simpa only [Set.mem_preimage, Set.mem_Ico] using this

sa_check_fwd fwd_gp_1 grid_preimage_span sh_gp_1 forbid [apply_pullback, apply_discrete_eq, grid_mem_Ico_iff, sh_gp_2, sh_gp_3]

theorem fwd_gp_2
    (hT : ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ),
      grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico ⌈(a - t₀) / Δ⌉ ⌈(b - t₀) / Δ⌉) :
    ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ), ∃ m n : ℤ, grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico m n := by
  intro t₀ Δ hΔ a b
  exact ⟨_, _, hT hΔ a b⟩

sa_check_fwd fwd_gp_2 grid_preimage_span sh_gp_2 forbid [apply_pullback, apply_discrete_eq, grid_mem_Ico_iff, sh_gp_1, sh_gp_3]

theorem fwd_gp_3
    (hT : ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ),
      grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico ⌈(a - t₀) / Δ⌉ ⌈(b - t₀) / Δ⌉) :
    ∀ (a b : ℝ), grid 0 1 ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  intro a b
  have := hT (t₀ := 0) (Δ := 1) one_pos a b
  simpa using this

sa_check_fwd fwd_gp_3 grid_preimage_span sh_gp_3 forbid [apply_pullback, apply_discrete_eq, grid_mem_Ico_iff, sh_gp_1, sh_gp_2]

theorem bwd_gp
    (h₁ : ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ) (k : ℤ),
      (a ≤ grid t₀ Δ k ∧ grid t₀ Δ k < b) ↔ (⌈(a - t₀) / Δ⌉ ≤ k ∧ k < ⌈(b - t₀) / Δ⌉))
    (h₂ : ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ), ∃ m n : ℤ, grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico m n)
    (h₃ : ∀ (a b : ℝ), grid 0 1 ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉) :
    ∀ {t₀ Δ : ℝ}, 0 < Δ → ∀ (a b : ℝ),
      grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico ⌈(a - t₀) / Δ⌉ ⌈(b - t₀) / Δ⌉ := by
  intro t₀ Δ hΔ a b
  have _ := @h₂
  have _ := h₃
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico]
  exact h₁ hΔ a b k

sa_check_bwd bwd_gp grid_preimage_span [sh_gp_1, sh_gp_2, sh_gp_3] forbid [apply_pullback, apply_discrete_eq, grid_mem_Ico_iff]

/-! ## Shadows for `apply_discrete_eq` -/

/-- NL: "commutes with resampling" — pointwise per target: intervening the
sampled schedule is sampling the intervened schedule. -/
theorem sh_ad_1 {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
    {t₀ Δ : ℝ} (hΔ : 0 < Δ) (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ) (j : T) :
    apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k j = apply P θ (grid t₀ Δ k) j := by
  simp only [apply, foldAt_gridPullback hΔ]

/-- NL facet: as an equality of sampled schedules (functions of the index). -/
theorem sh_ad_2 {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
    {t₀ Δ : ℝ} (hΔ : 0 < Δ) (P : Program ℝ T M) (θ : ℝ → T → V) :
    apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) = fun k => apply P θ (grid t₀ Δ k) := by
  funext k j
  exact sh_ad_1 hΔ P θ k j

/-- NL facet (unit grid). -/
theorem sh_ad_3 {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
    (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ) :
    apply (gridPullback 0 1 P) (fun k => θ (grid 0 1 k)) k = apply P θ (grid 0 1 k) := by
  funext j
  exact sh_ad_1 one_pos P θ k j

sa_check_shadow_free sh_ad_1 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_ad_2 [apply_pullback, grid_preimage_span, apply_discrete_eq]
sa_check_shadow_free sh_ad_3 [apply_pullback, grid_preimage_span, apply_discrete_eq]

theorem fwd_ad_1
    (hT : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k = apply P θ (grid t₀ Δ k)) :
    ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ) (j : T),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k j = apply P θ (grid t₀ Δ k) j := by
  intro T M V _ _ _ t₀ Δ hΔ P θ k j
  exact congrFun (hT hΔ P θ k) j

sa_check_fwd fwd_ad_1 apply_discrete_eq sh_ad_1 forbid [apply_pullback, grid_preimage_span, foldAt_gridPullback, sh_ad_2, sh_ad_3]

theorem fwd_ad_2
    (hT : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k = apply P θ (grid t₀ Δ k)) :
    ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) = fun k => apply P θ (grid t₀ Δ k) := by
  intro T M V _ _ _ t₀ Δ hΔ P θ
  funext k
  exact hT hΔ P θ k

sa_check_fwd fwd_ad_2 apply_discrete_eq sh_ad_2 forbid [apply_pullback, grid_preimage_span, foldAt_gridPullback, sh_ad_1, sh_ad_3]

theorem fwd_ad_3
    (hT : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k = apply P θ (grid t₀ Δ k)) :
    ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback 0 1 P) (fun k => θ (grid 0 1 k)) k = apply P θ (grid 0 1 k) := by
  intro T M V _ _ _ P θ k
  exact hT one_pos P θ k

sa_check_fwd fwd_ad_3 apply_discrete_eq sh_ad_3 forbid [apply_pullback, grid_preimage_span, foldAt_gridPullback, sh_ad_1, sh_ad_2]

theorem bwd_ad
    (h₁ : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ) (j : T),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k j = apply P θ (grid t₀ Δ k) j)
    (h₂ : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) = fun k => apply P θ (grid t₀ Δ k))
    (h₃ : ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback 0 1 P) (fun k => θ (grid 0 1 k)) k = apply P θ (grid 0 1 k)) :
    ∀ {T : Type v} {M : Type w} {V : Type x} [DecidableEq T] [PCM M] [HasAct M V]
      {t₀ Δ : ℝ}, 0 < Δ → ∀ (P : Program ℝ T M) (θ : ℝ → T → V) (k : ℤ),
      apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k = apply P θ (grid t₀ Δ k) := by
  intro T M V _ _ _ t₀ Δ hΔ P θ k
  have _ := @h₂
  have _ := @h₃
  funext j
  exact h₁ hΔ P θ k j

sa_check_bwd bwd_ad apply_discrete_eq [sh_ad_1, sh_ad_2, sh_ad_3] forbid [apply_pullback, grid_preimage_span, foldAt_gridPullback]

end CategoricalInterventionsProofs.SAPass.C15
