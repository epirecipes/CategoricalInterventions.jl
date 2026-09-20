import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Infer
import CategoricalInterventionsProofs.Semantics

/-!
# SA-Pass claim 23

NL claim: **"Inferring a program from a program's own output returns that output
when re-applied."**
Targets: `infer_putget`, `infer_putget_grid_step`.

Reading note: the sentence says the re-applied program returns "that output",
i.e. the observed schedule, with no restriction to grid points; the theorems
are stated at the *start of every cell* (`c.lo`) / at every *grid point*.  For
the sentence to hold at all times one needs the observed schedule to be
piecewise constant on the cells (span-only program, constant baseline, cells =
epochs), which is the first shadow below.
-/

namespace CategoricalInterventionsProofs.SAPass.C23

open CategoricalInterventionsProofs

universe u v w

/-- Glue: `foldAt_infer` at every time of a cell, not only at its start. -/
theorem foldAt_infer_mem {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] {cells : List (Span τ)} (hd : cells.Pairwise Span.Disjoint)
    {c : Span τ} (hc : c ∈ cells) {t : τ} (ht : c.mem t) (θ0 θ1 : τ → T → G) (j : T) :
    foldAt j (infer cells θ0 θ1) t = some ⟨θ1 c.lo j / θ0 c.lo j⟩ := by
  induction cells with
  | nil => simp at hc
  | cons c' rest ih =>
    have hdis : ∀ c'' ∈ rest, c'.Disjoint c'' := (List.pairwise_cons.mp hd).1
    have hrest := hd.of_cons
    simp only [infer, List.flatMap_cons]
    rw [← infer, foldAt_append, foldAt_inferCell]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [if_pos ht, foldAt_infer_eq_one]
      · simp [mul_one]
      · intro c'' hc'' hm
        exact (hdis c'' hc'').not_mem ht hm
    · have : ¬ c'.mem t := fun hm => (hdis c hc).not_mem hm ht
      rw [if_neg this, ih hrest hc]
      simp [one_mul]

/-! ## Shadows for `infer_putget` -/

/-- NL (full reading): inferring from a span-only program's own output on a
constant baseline, with the program's epochs as cells, and re-applying returns
that output at *every* time of every epoch. -/
theorem sh_ip_1 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (P : Program τ T (Multiplicative G)) (hP : SpanOnly P)
    (θ0 : T → G) (c : Span τ) (hc : c ∈ epochs P) (t : τ) (ht : c.mem t) (j : T) :
    apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t j =
      apply P (fun _ => θ0) t j := by
  have hd := epochs_pairwise_disjoint P
  simp only [apply, foldAt_infer_mem hd hc ht, actOpt_some, Multiplicative.act_def]
  change apply P (fun _ => θ0) c.lo j / θ0 j * θ0 j = _
  rw [div_mul_cancel]
  exact congrFun (apply_const_on_epoch hP hc (fun _ _ _ _ => rfl) (span_lo_mem c) ht) j

/-- NL: "returns that output when re-applied" — at the start of every cell, as
an equality of the whole target-vector. -/
theorem sh_ip_2 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (cells : List (Span τ)) (hd : cells.Pairwise Span.Disjoint)
    (c : Span τ) (hc : c ∈ cells) (θ0 θ1 : τ → T → G) :
    apply (infer cells θ0 θ1) θ0 c.lo = θ1 c.lo := by
  funext j
  simp only [apply, foldAt_infer_mem hd hc (span_lo_mem c), actOpt_some, Multiplicative.act_def]
  exact div_mul_cancel _ _

/-- NL facet: a single cell needs no disjointness hypothesis. -/
theorem sh_ip_3 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (c : Span τ) (θ0 θ1 : τ → T → G) (j : T) :
    apply (infer [c] θ0 θ1) θ0 c.lo j = θ1 c.lo j :=
  congrFun (sh_ip_2 [c] (List.pairwise_singleton _ _) c (List.mem_singleton_self c) θ0 θ1) j

/-- NL: "from a program's own output" — round trip at cell starts with
`θ1 := P ▷ θ0`. -/
theorem sh_ip_4 {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T]
    [Fintype T] [CommGroup G] (cells : List (Span τ)) (hd : cells.Pairwise Span.Disjoint)
    (c : Span τ) (hc : c ∈ cells) (P : Program τ T (Multiplicative G)) (θ0 : τ → T → G) (j : T) :
    apply (infer cells θ0 (apply P θ0)) θ0 c.lo j = apply P θ0 c.lo j :=
  congrFun (sh_ip_2 cells hd c hc θ0 (apply P θ0)) j

sa_check_shadow_free sh_ip_1 [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]
sa_check_shadow_free sh_ip_2 [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]
sa_check_shadow_free sh_ip_3 [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]
sa_check_shadow_free sh_ip_4 [infer_putget, infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full]

/- `fwd_ip_1` (infer_putget ⇒ sh_ip_1) is OMITTED: the target speaks only about
the start `c.lo` of a cell; the value at other times of the cell is not a
consequence of it.  See SA-PASS.md. -/

theorem fwd_ip_2
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {cells : List (Span τ)}, List.Pairwise Span.Disjoint cells →
      ∀ {c : Span τ}, c ∈ cells → ∀ (θ0 θ1 : τ → T → G) (j : T),
      apply (infer cells θ0 θ1) θ0 c.lo j = θ1 c.lo j) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (cells : List (Span τ)), cells.Pairwise Span.Disjoint →
      ∀ (c : Span τ), c ∈ cells → ∀ (θ0 θ1 : τ → T → G),
      apply (infer cells θ0 θ1) θ0 c.lo = θ1 c.lo := by
  intro τ T G _ _ _ _ cells hd c hc θ0 θ1
  funext j
  exact hT hd hc θ0 θ1 j

sa_check_fwd fwd_ip_2 infer_putget sh_ip_2
  forbid [infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full, foldAt_infer, foldAt_infer_mem, sh_ip_1, sh_ip_3, sh_ip_4]

theorem fwd_ip_3
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {cells : List (Span τ)}, List.Pairwise Span.Disjoint cells →
      ∀ {c : Span τ}, c ∈ cells → ∀ (θ0 θ1 : τ → T → G) (j : T),
      apply (infer cells θ0 θ1) θ0 c.lo j = θ1 c.lo j) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (c : Span τ) (θ0 θ1 : τ → T → G) (j : T),
      apply (infer [c] θ0 θ1) θ0 c.lo j = θ1 c.lo j := by
  intro τ T G _ _ _ _ c θ0 θ1 j
  exact hT (List.pairwise_singleton _ _) (List.mem_singleton_self c) θ0 θ1 j

sa_check_fwd fwd_ip_3 infer_putget sh_ip_3
  forbid [infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full, foldAt_infer, foldAt_infer_mem, sh_ip_1, sh_ip_2, sh_ip_4]

theorem fwd_ip_4
    (hT : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {cells : List (Span τ)}, List.Pairwise Span.Disjoint cells →
      ∀ {c : Span τ}, c ∈ cells → ∀ (θ0 θ1 : τ → T → G) (j : T),
      apply (infer cells θ0 θ1) θ0 c.lo j = θ1 c.lo j) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (cells : List (Span τ)), cells.Pairwise Span.Disjoint →
      ∀ (c : Span τ), c ∈ cells → ∀ (P : Program τ T (Multiplicative G)) (θ0 : τ → T → G) (j : T),
      apply (infer cells θ0 (apply P θ0)) θ0 c.lo j = apply P θ0 c.lo j := by
  intro τ T G _ _ _ _ cells hd c hc P θ0 j
  exact hT hd hc θ0 (apply P θ0) j

sa_check_fwd fwd_ip_4 infer_putget sh_ip_4
  forbid [infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full, foldAt_infer, foldAt_infer_mem, sh_ip_1, sh_ip_2, sh_ip_3]

theorem bwd_ip
    (h₁ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (P : Program τ T (Multiplicative G)), SpanOnly P → ∀ (θ0 : T → G)
      (c : Span τ), c ∈ epochs P → ∀ (t : τ), c.mem t → ∀ (j : T),
      apply (infer (epochs P) (fun _ => θ0) (apply P (fun _ => θ0))) (fun _ => θ0) t j =
        apply P (fun _ => θ0) t j)
    (h₂ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (cells : List (Span τ)), cells.Pairwise Span.Disjoint →
      ∀ (c : Span τ), c ∈ cells → ∀ (θ0 θ1 : τ → T → G),
      apply (infer cells θ0 θ1) θ0 c.lo = θ1 c.lo)
    (h₃ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (c : Span τ) (θ0 θ1 : τ → T → G) (j : T),
      apply (infer [c] θ0 θ1) θ0 c.lo j = θ1 c.lo j)
    (h₄ : ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] (cells : List (Span τ)), cells.Pairwise Span.Disjoint →
      ∀ (c : Span τ), c ∈ cells → ∀ (P : Program τ T (Multiplicative G)) (θ0 : τ → T → G) (j : T),
      apply (infer cells θ0 (apply P θ0)) θ0 c.lo j = apply P θ0 c.lo j) :
    ∀ {τ : Type u} {T : Type v} {G : Type w} [LinearOrder τ] [DecidableEq T] [Fintype T]
      [CommGroup G] {cells : List (Span τ)}, List.Pairwise Span.Disjoint cells →
      ∀ {c : Span τ}, c ∈ cells → ∀ (θ0 θ1 : τ → T → G) (j : T),
      apply (infer cells θ0 θ1) θ0 c.lo j = θ1 c.lo j := by
  intro τ T G _ _ _ _ cells hd c hc θ0 θ1 j
  have _ := @h₁
  have _ := @h₃
  have _ := @h₄
  exact congrFun (h₂ cells hd c hc θ0 θ1) j

sa_check_bwd bwd_ip infer_putget [sh_ip_1, sh_ip_2, sh_ip_3, sh_ip_4]
  forbid [infer_putget_grid_step, infer_putget_grid, infer_putget_grid_full, foldAt_infer, foldAt_infer_mem]

/-! ## Shadows for `infer_putget_grid_step` -/

/-- NL: "from a program's own output … returns that output" — round trip on a
real grid, at every grid point. -/
theorem sh_ig_1 {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G]
    (grid : List ℝ) (hg : grid.Pairwise (· < ·)) (step : ℝ) (hstep : 0 < step)
    (P : Program ℝ T (Multiplicative G)) (θ0 : ℝ → T → G) :
    ∀ k ∈ grid, apply (inferGridStep grid step θ0 (apply P θ0)) θ0 k = apply P θ0 k :=
  infer_putget_grid_full hg (fun _ hk =>
    lt_of_le_of_lt (le_getLastD_of_sorted hg 0 hk) (lt_add_of_pos_right _ hstep)) θ0 _

/-- NL facet: pointwise per target. -/
theorem sh_ig_2 {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G]
    (grid : List ℝ) (hg : grid.Pairwise (· < ·)) (step : ℝ) (hstep : 0 < step)
    (θ0 θ1 : ℝ → T → G) : ∀ k ∈ grid, ∀ j, apply (inferGridStep grid step θ0 θ1) θ0 k j = θ1 k j :=
  fun k hk j => congrFun (infer_putget_grid_full hg (fun _ hk =>
    lt_of_le_of_lt (le_getLastD_of_sorted hg 0 hk) (lt_add_of_pos_right _ hstep)) θ0 θ1 k hk) j

/-- NL facet: the *last* grid point is included (the Julia `infer` closes the
last cell one step later). -/
theorem sh_ig_3 {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G]
    (grid : List ℝ) (hg : grid.Pairwise (· < ·)) (step : ℝ) (hstep : 0 < step)
    (θ0 θ1 : ℝ → T → G) (h : grid ≠ []) :
    apply (inferGridStep grid step θ0 θ1) θ0 (grid.getLast h) = θ1 (grid.getLast h) :=
  infer_putget_grid_full hg (fun _ hk =>
    lt_of_le_of_lt (le_getLastD_of_sorted hg 0 hk) (lt_add_of_pos_right _ hstep)) θ0 θ1 _
    (List.getLast_mem h)

/- The grid shadows are proved through `infer_putget_grid_full`, which itself
rests on `infer_putget` (the other target of this row); they are independent
of their own target `infer_putget_grid_step`. -/
sa_check_shadow_free sh_ig_1 [infer_putget_grid_step]
sa_check_shadow_free sh_ig_2 [infer_putget_grid_step]
sa_check_shadow_free sh_ig_3 [infer_putget_grid_step]

theorem fwd_ig_1
    (hT : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] {grid : List ℝ},
      List.Pairwise (fun x1 x2 => x1 < x2) grid → ∀ {step : ℝ}, 0 < step →
      ∀ (θ0 θ1 : ℝ → T → G), ∀ k ∈ grid, apply (inferGridStep grid step θ0 θ1) θ0 k = θ1 k) :
    ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step →
      ∀ (P : Program ℝ T (Multiplicative G)) (θ0 : ℝ → T → G),
      ∀ k ∈ grid, apply (inferGridStep grid step θ0 (apply P θ0)) θ0 k = apply P θ0 k := by
  intro T G _ _ _ grid hg step hstep P θ0 k hk
  exact hT hg hstep θ0 (apply P θ0) k hk

sa_check_fwd fwd_ig_1 infer_putget_grid_step sh_ig_1
  forbid [infer_putget, infer_putget_grid, infer_putget_grid_full, sh_ig_2, sh_ig_3]

theorem fwd_ig_2
    (hT : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] {grid : List ℝ},
      List.Pairwise (fun x1 x2 => x1 < x2) grid → ∀ {step : ℝ}, 0 < step →
      ∀ (θ0 θ1 : ℝ → T → G), ∀ k ∈ grid, apply (inferGridStep grid step θ0 θ1) θ0 k = θ1 k) :
    ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step → ∀ (θ0 θ1 : ℝ → T → G),
      ∀ k ∈ grid, ∀ j, apply (inferGridStep grid step θ0 θ1) θ0 k j = θ1 k j := by
  intro T G _ _ _ grid hg step hstep θ0 θ1 k hk j
  exact congrFun (hT hg hstep θ0 θ1 k hk) j

sa_check_fwd fwd_ig_2 infer_putget_grid_step sh_ig_2
  forbid [infer_putget, infer_putget_grid, infer_putget_grid_full, sh_ig_1, sh_ig_3]

theorem fwd_ig_3
    (hT : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] {grid : List ℝ},
      List.Pairwise (fun x1 x2 => x1 < x2) grid → ∀ {step : ℝ}, 0 < step →
      ∀ (θ0 θ1 : ℝ → T → G), ∀ k ∈ grid, apply (inferGridStep grid step θ0 θ1) θ0 k = θ1 k) :
    ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step → ∀ (θ0 θ1 : ℝ → T → G) (h : grid ≠ []),
      apply (inferGridStep grid step θ0 θ1) θ0 (grid.getLast h) = θ1 (grid.getLast h) := by
  intro T G _ _ _ grid hg step hstep θ0 θ1 h
  exact hT hg hstep θ0 θ1 _ (List.getLast_mem h)

sa_check_fwd fwd_ig_3 infer_putget_grid_step sh_ig_3
  forbid [infer_putget, infer_putget_grid, infer_putget_grid_full, sh_ig_1, sh_ig_2]

theorem bwd_ig
    (h₁ : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step →
      ∀ (P : Program ℝ T (Multiplicative G)) (θ0 : ℝ → T → G),
      ∀ k ∈ grid, apply (inferGridStep grid step θ0 (apply P θ0)) θ0 k = apply P θ0 k)
    (h₂ : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step → ∀ (θ0 θ1 : ℝ → T → G),
      ∀ k ∈ grid, ∀ j, apply (inferGridStep grid step θ0 θ1) θ0 k j = θ1 k j)
    (h₃ : ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] (grid : List ℝ),
      grid.Pairwise (· < ·) → ∀ (step : ℝ), 0 < step → ∀ (θ0 θ1 : ℝ → T → G) (h : grid ≠ []),
      apply (inferGridStep grid step θ0 θ1) θ0 (grid.getLast h) = θ1 (grid.getLast h)) :
    ∀ {T : Type v} {G : Type w} [DecidableEq T] [Fintype T] [CommGroup G] {grid : List ℝ},
      List.Pairwise (fun x1 x2 => x1 < x2) grid → ∀ {step : ℝ}, 0 < step →
      ∀ (θ0 θ1 : ℝ → T → G), ∀ k ∈ grid, apply (inferGridStep grid step θ0 θ1) θ0 k = θ1 k := by
  intro T G _ _ _ grid hg step hstep θ0 θ1 k hk
  have _ := @h₁
  have _ := @h₃
  funext j
  exact h₂ grid hg step hstep θ0 θ1 k hk j

sa_check_bwd bwd_ig infer_putget_grid_step [sh_ig_1, sh_ig_2, sh_ig_3]
  forbid [infer_putget, infer_putget_grid, infer_putget_grid_full]

end CategoricalInterventionsProofs.SAPass.C23
