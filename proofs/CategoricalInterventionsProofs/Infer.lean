import CategoricalInterventionsProofs.Transport
import CategoricalInterventionsProofs.Epoch
import Mathlib.Data.Real.Basic

/-!
# Inference: recovering a program from schedules

Given a baseline schedule `θ₀` and an observed schedule `θ₁` over a
multiplicative algebra with division (a `CommGroup`), `infer` produces a
program whose action on `θ₀` reproduces `θ₁` on a grid.

Simplification (documented): the version proved here produces one span atom
per grid *cell* and target, with effect `θ₁ / θ₀` at the cell's start; it does
not merge adjacent cells with equal ratio into maximal runs.  The put-get law
`infer_putget` is proved pointwise at the start of every cell.  Cells are a list
of pairwise-disjoint spans, e.g. `consecutiveSpans grid` for a sorted grid
(`consecutiveSpans_pairwise_disjoint`); see `infer_putget_grid`.
-/

namespace CategoricalInterventionsProofs

variable {τ T G : Type*} [LinearOrder τ] [DecidableEq T] [Fintype T] [CommGroup G]

omit [Fintype T] in
/-- The fold over one atom per target of a duplicate-free target list. -/
theorem foldAt_map_targets {M : Type*} [PCM M] {L : List T} (hL : L.Nodup) (S : Support τ)
    (e : T → M) (j : T) (t : τ) :
    foldAt j (L.map fun i => (⟨0, i, S, e i⟩ : Atom τ T M)) t =
      if S.mem t ∧ j ∈ L then some (e j) else some one := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx : x ∉ L := (List.nodup_cons.mp hL).1
    have ih := ih (List.nodup_cons.mp hL).2
    simp only [List.map_cons]
    rw [foldAt_cons, ih]
    by_cases hm : S.mem t
    · by_cases hj : x = j
      · subst hj
        simp [hm, hx, mul_one]
      · have : j ∈ x :: L ↔ j ∈ L := by
          simp [List.mem_cons, Ne.symm hj]
        simp [hm, hj, this]
    · simp [hm]

/-- The atoms for one cell: on every target, scale by `θ₁ / θ₀` at the cell's start. -/
noncomputable def inferCell (θ0 θ1 : τ → T → G) (c : Span τ) : Program τ T (Multiplicative G) :=
  (Finset.univ : Finset T).toList.map fun j => ⟨0, j, .span c, ⟨θ1 c.lo j / θ0 c.lo j⟩⟩

/-- The inferred program: one cell's atoms per cell. -/
noncomputable def infer (cells : List (Span τ)) (θ0 θ1 : τ → T → G) :
    Program τ T (Multiplicative G) :=
  cells.flatMap (inferCell θ0 θ1)

omit [DecidableEq T] in
theorem mem_infer {cells : List (Span τ)} {θ0 θ1 : τ → T → G}
    {a : Atom τ T (Multiplicative G)} (h : a ∈ infer cells θ0 θ1) :
    ∃ c ∈ cells, a.support = .span c := by
  simp only [infer, inferCell, List.mem_flatMap, List.mem_map] at h
  obtain ⟨c, hc, j, -, rfl⟩ := h
  exact ⟨c, hc, rfl⟩

theorem foldAt_inferCell (θ0 θ1 : τ → T → G) (c : Span τ) (j : T) (t : τ) :
    foldAt j (inferCell θ0 θ1 c) t =
      if c.mem t then some ⟨θ1 c.lo j / θ0 c.lo j⟩ else some one := by
  rw [inferCell, foldAt_map_targets (Finset.nodup_toList _)]
  simp [Finset.mem_toList]

theorem foldAt_infer_eq_one {cells : List (Span τ)} (θ0 θ1 : τ → T → G) {t : τ}
    (h : ∀ c ∈ cells, ¬ c.mem t) (j : T) : foldAt j (infer cells θ0 θ1) t = some one :=
  foldAt_eq_one_of_not_active j _ t (fun a ha => by
    obtain ⟨c, hc, hs⟩ := mem_infer ha
    rw [hs]
    exact h c hc)

/-- At the start of a cell, the inferred fold on `j` is exactly the ratio there. -/
theorem foldAt_infer {cells : List (Span τ)} (hd : cells.Pairwise Span.Disjoint)
    {c : Span τ} (hc : c ∈ cells) (θ0 θ1 : τ → T → G) (j : T) :
    foldAt j (infer cells θ0 θ1) c.lo = some ⟨θ1 c.lo j / θ0 c.lo j⟩ := by
  induction cells with
  | nil => simp at hc
  | cons c' rest ih =>
    have hdis : ∀ c'' ∈ rest, c'.Disjoint c'' := (List.pairwise_cons.mp hd).1
    have hrest := hd.of_cons
    simp only [infer, List.flatMap_cons]
    rw [← infer, foldAt_append, foldAt_inferCell]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [if_pos (span_lo_mem c), foldAt_infer_eq_one]
      · simp [mul_one]
      · intro c'' hc'' hm
        exact (hdis c'' hc'').not_mem (span_lo_mem c) hm
    · have : ¬ c'.mem c.lo := fun hm => (hdis c hc).not_mem hm (span_lo_mem c)
      rw [if_neg this, ih hrest hc]
      simp [one_mul]

/-- **Put-get.** Applying the inferred program to the baseline reproduces the
observed schedule at the start of every cell. -/
theorem infer_putget {cells : List (Span τ)} (hd : cells.Pairwise Span.Disjoint)
    {c : Span τ} (hc : c ∈ cells) (θ0 θ1 : τ → T → G) (j : T) :
    apply (infer cells θ0 θ1) θ0 c.lo j = θ1 c.lo j := by
  simp only [apply, foldAt_infer hd hc, actOpt_some, Multiplicative.act_def]
  exact div_mul_cancel _ _

/-- Inference on a time grid: cells are the consecutive spans of the grid. -/
noncomputable def inferGrid (grid : List τ) (θ0 θ1 : τ → T → G) :
    Program τ T (Multiplicative G) :=
  infer (consecutiveSpans grid) θ0 θ1

/-- **Put-get on a sorted grid.** At the start of every grid cell (every grid point
but the last), applying the inferred program to `θ₀` gives `θ₁`. -/
theorem infer_putget_grid {grid : List τ} (hg : grid.Pairwise (· < ·))
    {c : Span τ} (hc : c ∈ consecutiveSpans grid) (θ0 θ1 : τ → T → G) (j : T) :
    apply (inferGrid grid θ0 θ1) θ0 c.lo j = θ1 c.lo j :=
  infer_putget (consecutiveSpans_pairwise_disjoint hg) hc θ0 θ1 j

/-- Inference on a grid extended by a final end time `tEnd` after the last grid
point, so that the last grid point also starts a cell (as the Julia `infer` does
by ending the last span one step after the last time). -/
noncomputable def inferGridFull (grid : List τ) (tEnd : τ) (θ0 θ1 : τ → T → G) :
    Program τ T (Multiplicative G) :=
  inferGrid (grid ++ [tEnd]) θ0 θ1

/-- **Put-get on every grid point.** For a sorted grid and an end time beyond all
grid points, applying the inferred program to `θ₀` gives `θ₁` at every grid
point, including the last. -/
theorem infer_putget_grid_full {grid : List τ} (hg : grid.Pairwise (· < ·)) {tEnd : τ}
    (hend : ∀ k ∈ grid, k < tEnd) (θ0 θ1 : τ → T → G) :
    ∀ k ∈ grid, apply (inferGridFull grid tEnd θ0 θ1) θ0 k = θ1 k := by
  intro k hk
  funext j
  have hsorted : (grid ++ [tEnd]).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    exact ⟨hg, List.pairwise_singleton _ _, fun a ha b hb => by
      rw [List.mem_singleton] at hb; subst hb; exact hend a ha⟩
  obtain ⟨c, hc, hlo⟩ := exists_consecutiveSpan_lo_eq hsorted
    (List.mem_append_left _ hk) ⟨tEnd, List.mem_append_right _ List.mem_cons_self, hend k hk⟩
  rw [← hlo]
  exact infer_putget_grid hsorted hc θ0 θ1 j

/-- The last element of a sorted list bounds all its elements. -/
theorem le_getLastD_of_sorted {l : List τ} (hl : l.Pairwise (· < ·)) (d : τ) {k : τ}
    (hk : k ∈ l) : k ≤ l.getLastD d := by
  induction l generalizing d k with
  | nil => simp at hk
  | cons a rest ih =>
    rw [List.getLastD_cons]
    have ha_lt : ∀ c ∈ rest, a < c := (List.pairwise_cons.mp hl).1
    rcases List.mem_cons.mp hk with hka | hkr
    · subst hka
      cases rest with
      | nil => simp
      | cons b rest' =>
        exact le_trans (le_of_lt (ha_lt b List.mem_cons_self))
          (ih hl.of_cons k List.mem_cons_self)
    · exact ih hl.of_cons a hkr

/-- Inference on a real grid with a positive step: the last cell ends one step
after the last grid point. -/
noncomputable def inferGridStep (grid : List ℝ) (step : ℝ) (θ0 θ1 : ℝ → T → G) :
    Program ℝ T (Multiplicative G) :=
  inferGridFull grid (grid.getLastD 0 + step) θ0 θ1

/-- **Put-get on a real grid with a positive step**, at every grid point. -/
theorem infer_putget_grid_step {grid : List ℝ} (hg : grid.Pairwise (· < ·)) {step : ℝ}
    (hstep : 0 < step) (θ0 θ1 : ℝ → T → G) :
    ∀ k ∈ grid, apply (inferGridStep grid step θ0 θ1) θ0 k = θ1 k :=
  infer_putget_grid_full hg (fun _ hk =>
    lt_of_le_of_lt (le_getLastD_of_sorted hg 0 hk) (lt_add_of_pos_right _ hstep)) θ0 θ1

end CategoricalInterventionsProofs
