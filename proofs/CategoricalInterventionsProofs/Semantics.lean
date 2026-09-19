import CategoricalInterventionsProofs.Epoch
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Semantics on schedules

A *schedule* is a function `θ : τ → T → V`.  A program acts pointwise:
`(P ▷ θ) t j = foldAt j P t ▷ θ t j`.  The definition is total (an undefined
fold leaves the value untouched); the theorems assume conflict-freeness where
they need it.

Theorems: identity, locality, homomorphism, commutativity, naturality under
pullback along any `r : τ' → τ`, the grid-sampling formula, and piecewise
constancy on epochs.
-/

namespace CategoricalInterventionsProofs

variable {τ T M V : Type*} [LinearOrder τ] [DecidableEq T] [PCM M]

section Def
variable [HasAct M V]

/-- Act by an optional effect (`none` acts trivially). -/
def actOpt (o : Option M) (v : V) : V :=
  match o with
  | some m => act m v
  | none => v

omit [PCM M] in
@[simp] theorem actOpt_some (m : M) (v : V) : actOpt (some m) v = act m v := rfl
omit [PCM M] in
@[simp] theorem actOpt_none (v : V) : actOpt (none : Option M) v = v := rfl

/-- The action of a program on a schedule. -/
def apply (P : Program τ T M) (θ : τ → T → V) (t : τ) (j : T) : V :=
  actOpt (foldAt j P t) (θ t j)

end Def

section Laws
variable [PCMAction M V]

/-- **Identity.** The empty program acts trivially. -/
theorem apply_nil (θ : τ → T → V) : apply ([] : Program τ T M) θ = θ := by
  funext t j
  simp [apply, act_one]

/-- **Locality.** If no atom is active at `t`, the schedule is unchanged at `t`. -/
theorem apply_local {P : Program τ T M} {t : τ} (h : ∀ a ∈ P, ¬ a.support.mem t)
    (θ : τ → T → V) : apply P θ t = θ t := by
  funext j
  simp [apply, foldAt_eq_one_of_not_active j P t h, act_one]

/-- **Homomorphism.** Applying a conflict-free composite is applying the parts in
sequence: `(P ++ Q) ▷ θ = Q ▷ (P ▷ θ)`. -/
theorem apply_append {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) (θ : τ → T → V) :
    apply (P ++ Q) θ = apply Q (apply P θ) := by
  funext t j
  have h1 := h t j
  rw [foldAt_append] at h1
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at h1
    · rw [hP, hQ] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      exact act_mul' (V := V) (θ t j) hc

/-- The other order: `(P ++ Q) ▷ θ = P ▷ (Q ▷ θ)`. -/
theorem apply_append' {P Q : Program τ T M} (h : ConflictFree (P ++ Q)) (θ : τ → T → V) :
    apply (P ++ Q) θ = apply P (apply Q θ) := by
  funext t j
  have h1 := h t j
  rw [foldAt_append] at h1
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ : foldAt j Q t with _ | b
    · simp [hP, hQ] at h1
    · rw [hP, hQ] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      exact act_mul (V := V) _ _ _ (θ t j) hc

end Laws

/-- **Homomorphism for `Affine`.** For programs over `Affine V M`, sequential
application agrees with the composite when the later program `Q` is purely
relative (no absolute assignments): "set, then scale". -/
theorem apply_append_affine {M : Type*} [PCM M] [PCMAction M V]
    {P Q : Program τ T (Affine V M)} (h : ConflictFree (P ++ Q))
    (hQ : ∀ a ∈ Q, a.effect.abs = none) (θ : τ → T → V) :
    apply (P ++ Q) θ = apply Q (apply P θ) := by
  funext t j
  have h1 := h t j
  rw [foldAt_append] at h1
  simp only [apply, foldAt_append]
  rcases hP : foldAt j P t with _ | a
  · simp [hP] at h1
  · rcases hQ' : foldAt j Q t with _ | b
    · simp [hP, hQ'] at h1
    · rw [hP, hQ'] at h1
      simp only [Option.bind_some] at h1 ⊢
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
      rw [hc]
      simp only [actOpt_some]
      have hb : b.abs = none := by
        have hall : ∀ e ∈ effectsAt j Q t, e.abs = none := by
          intro e he
          simp only [effectsAt, List.mem_map, List.mem_filter, mem_active] at he
          obtain ⟨a', ⟨⟨ha', -⟩, -⟩, rfl⟩ := he
          exact hQ a' ha'
        exact (Affine.fold_abs_none_iff hQ').mpr hall
      exact Affine.act_mul_of_relative (θ t j) hb hc

section Comm
variable [HasAct M V]

/-- **Commutativity.** Composition order is irrelevant for the action (this holds
for every program, conflict-free or not, since folds are permutation-invariant). -/
theorem apply_comm (P Q : Program τ T M) (θ : τ → T → V) :
    apply (P ++ Q) θ = apply (Q ++ P) θ := by
  funext t j
  simp only [apply]
  rw [foldAt_perm List.perm_append_comm]

end Comm

section Pullback
variable [HasAct M V]

/-! ## Naturality: pullback along a reparametrisation -/

/-- A generalised atom whose support is an arbitrary set of times. This is the
target of pullback, since preimages of spans need not be spans. -/
structure GAtom (τ' T M : Type*) where
  id : ℕ
  target : T
  support : Set τ'
  effect : M

/-- A generalised program. -/
abbrev GProgram (τ' T M : Type*) := List (GAtom τ' T M)

open Classical in
/-- The action of a generalised program. -/
noncomputable def gapply {τ' : Type*} (Q : GProgram τ' T M) (θ : τ' → T → V) (t : τ') (j : T) : V :=
  actOpt (foldList (((Q.filter (fun a => decide (t ∈ a.support))).filter
    (fun a => decide (a.target = j))).map (·.effect))) (θ t j)

/-- Pull a program back along `r : τ' → τ`: supports become preimages. -/
def pullback {τ' : Type*} (r : τ' → τ) (P : Program τ T M) : GProgram τ' T M :=
  P.map fun a => ⟨a.id, a.target, r ⁻¹' a.support.memSet, a.effect⟩

/-- View an ordinary program as a generalised one. -/
def Program.toG (P : Program τ T M) : GProgram τ T M :=
  P.map fun a => ⟨a.id, a.target, a.support.memSet, a.effect⟩

omit [DecidableEq T] [PCM M] in
theorem gapply_filter_map {τ' : Type*} (P : Program τ T M) (g : Atom τ T M → GAtom τ' T M)
    (p₁ : Atom τ T M → Bool) (p₂ : Atom τ T M → Bool) (q₁ q₂ : GAtom τ' T M → Bool)
    (h₁ : ∀ a ∈ P, q₁ (g a) = p₁ a) (h₂ : ∀ a ∈ P, q₂ (g a) = p₂ a)
    (heff : ∀ a, (g a).effect = a.effect) :
    (((P.map g).filter q₁).filter q₂).map (·.effect) =
      ((P.filter p₁).filter p₂).map (·.effect) := by
  rw [List.filter_map, List.filter_map, List.map_map]
  rw [List.filter_congr (p := q₁ ∘ g) (q := p₁) h₁]
  rw [List.filter_congr (p := q₂ ∘ g) (q := p₂)
    (fun a ha => h₂ a (List.mem_of_mem_filter ha))]
  apply List.map_congr_left
  intro a _
  exact heff a

/-- **Naturality.** Application commutes with pullback along any `r : τ' → τ`:
`(P ▷ θ) ∘ r = (r^* P) ▷ (θ ∘ r)`. -/
theorem apply_pullback {τ' : Type*} (r : τ' → τ) (P : Program τ T M) (θ : τ → T → V) :
    (fun t' => apply P θ (r t')) = gapply (pullback r P) (fun t' => θ (r t')) := by
  funext t' j
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

/-- The generalised semantics agrees with the ordinary one on ordinary programs. -/
theorem gapply_toG (P : Program τ T M) (θ : τ → T → V) : gapply P.toG θ = apply P θ := by
  funext t j
  simp only [apply, gapply, foldAt, effectsAt, active, Program.toG]
  congr 2
  apply gapply_filter_map
  · intro a _
    exact decide_eq_decide.mpr Iff.rfl
  · intro a _
    rfl
  · intro a
    rfl

/-! ## Grid sampling -/

/-- The grid `k ↦ t₀ + k Δ`. -/
def grid (t₀ Δ : ℝ) (k : ℤ) : ℝ := t₀ + k * Δ

theorem grid_mem_Ico_iff {t₀ Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) (k : ℤ) :
    (a ≤ grid t₀ Δ k ∧ grid t₀ Δ k < b) ↔ (⌈(a - t₀) / Δ⌉ ≤ k ∧ k < ⌈(b - t₀) / Δ⌉) := by
  simp only [grid, Int.ceil_le, Int.lt_ceil, div_le_iff₀ hΔ, lt_div_iff₀ hΔ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Grid sampling.** The preimage of a span `[a, b)` under the grid `k ↦ t₀ + kΔ`
(`Δ > 0`) is the integer span `[⌈(a − t₀)/Δ⌉, ⌈(b − t₀)/Δ⌉)`. -/
theorem grid_preimage_span {t₀ Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) :
    grid t₀ Δ ⁻¹' Set.Ico a b = Set.Ico ⌈(a - t₀) / Δ⌉ ⌈(b - t₀) / Δ⌉ := by
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico]
  exact grid_mem_Ico_iff hΔ a b k

theorem grid_eq_iff {t₀ Δ : ℝ} (hΔ : 0 < Δ) (s : ℝ) (k : ℤ) :
    grid t₀ Δ k = s ↔ (k : ℝ) = (s - t₀) / Δ := by
  rw [eq_div_iff hΔ.ne']
  simp only [grid]
  constructor <;> intro h <;> linarith

/-- Pull one atom back to the grid: a span becomes the ceiling-endpoint span (or is
dropped if that is empty); an instant survives iff it lies on the grid. -/
noncomputable def gridPullbackAtom (t₀ Δ : ℝ) (a : Atom ℝ T M) : Option (Atom ℤ T M) :=
  match a.support with
  | .span s =>
    if h : ⌈(s.lo - t₀) / Δ⌉ < ⌈(s.hi - t₀) / Δ⌉ then
      some ⟨a.id, a.target, .span ⟨_, _, h⟩, a.effect⟩
    else none
  | .instant i =>
    if grid t₀ Δ ⌈(i.time - t₀) / Δ⌉ = i.time then
      some ⟨a.id, a.target, .instant ⟨⌈(i.time - t₀) / Δ⌉⟩, a.effect⟩
    else none

/-- Pull a program back to the grid. -/
noncomputable def gridPullback (t₀ Δ : ℝ) (P : Program ℝ T M) : Program ℤ T M :=
  P.filterMap (gridPullbackAtom t₀ Δ)

omit [DecidableEq T] [PCM M] in
theorem gridPullbackAtom_span (t₀ Δ : ℝ) {a : Atom ℝ T M} {s : Span ℝ}
    (hs : a.support = .span s) :
    gridPullbackAtom t₀ Δ a =
      if h : ⌈(s.lo - t₀) / Δ⌉ < ⌈(s.hi - t₀) / Δ⌉ then
        some ⟨a.id, a.target, .span ⟨_, _, h⟩, a.effect⟩
      else none := by
  unfold gridPullbackAtom
  rw [hs]

omit [DecidableEq T] [PCM M] in
theorem gridPullbackAtom_instant (t₀ Δ : ℝ) {a : Atom ℝ T M} {i : Instant ℝ}
    (hs : a.support = .instant i) :
    gridPullbackAtom t₀ Δ a =
      if grid t₀ Δ ⌈(i.time - t₀) / Δ⌉ = i.time then
        some ⟨a.id, a.target, .instant ⟨⌈(i.time - t₀) / Δ⌉⟩, a.effect⟩
      else none := by
  unfold gridPullbackAtom
  rw [hs]

omit [DecidableEq T] [PCM M] in
theorem gridPullbackAtom_some {t₀ Δ : ℝ} (hΔ : 0 < Δ) {a : Atom ℝ T M} {a' : Atom ℤ T M}
    (h : gridPullbackAtom t₀ Δ a = some a') :
    a'.target = a.target ∧ a'.effect = a.effect ∧
      ∀ k, a'.support.mem k ↔ a.support.mem (grid t₀ Δ k) := by
  rcases hs : a.support with s | i
  · rw [gridPullbackAtom_span t₀ Δ hs] at h
    split_ifs at h with hlt
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      intro k
      simp only [Support.mem_span, Span.mem]
      exact (grid_mem_Ico_iff hΔ s.lo s.hi k).symm
  · rw [gridPullbackAtom_instant t₀ Δ hs] at h
    split_ifs at h with hg
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      intro k
      simp only [Support.mem_instant]
      constructor
      · rintro rfl
        exact hg
      · intro hk
        have h1 := (grid_eq_iff hΔ i.time k).mp hk
        have h2 := (grid_eq_iff hΔ i.time _).mp hg
        exact_mod_cast h1.trans h2.symm

omit [DecidableEq T] [PCM M] in
theorem gridPullbackAtom_none {t₀ Δ : ℝ} (hΔ : 0 < Δ) {a : Atom ℝ T M}
    (h : gridPullbackAtom t₀ Δ a = none) (k : ℤ) : ¬ a.support.mem (grid t₀ Δ k) := by
  rcases hs : a.support with s | i
  · rw [gridPullbackAtom_span t₀ Δ hs] at h
    split_ifs at h with hlt
    simp only [Support.mem_span, Span.mem]
    rw [grid_mem_Ico_iff hΔ]
    rintro ⟨h1, h2⟩
    exact hlt (lt_of_le_of_lt h1 h2)
  · rw [gridPullbackAtom_instant t₀ Δ hs] at h
    split_ifs at h with hg
    simp only [Support.mem_instant]
    intro hk
    apply hg
    have h1 := (grid_eq_iff hΔ i.time k).mp hk
    have : ⌈(i.time - t₀) / Δ⌉ = k := by
      rw [← h1, Int.ceil_intCast]
    rw [this]
    exact hk

/-- The fold of the grid pullback at `k` is the fold of the original at `grid k`. -/
theorem foldAt_gridPullback {t₀ Δ : ℝ} (hΔ : 0 < Δ) (j : T) (P : Program ℝ T M) (k : ℤ) :
    foldAt j (gridPullback t₀ Δ P) k = foldAt j P (grid t₀ Δ k) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    simp only [gridPullback, List.filterMap_cons]
    rcases h : gridPullbackAtom t₀ Δ a with _ | a'
    · rw [← gridPullback, ih, foldAt_cons]
      have := gridPullbackAtom_none hΔ h k
      simp [this]
    · obtain ⟨ht, he, hm⟩ := gridPullbackAtom_some hΔ h
      rw [foldAt_cons, foldAt_cons, ← gridPullback, ih]
      simp only [hm, ht, he]

/-- **Discrete application.** Applying the grid pullback at `k` is applying the
original program at `grid k`: one program serves both continuous and discrete
models. -/
theorem apply_discrete_eq {t₀ Δ : ℝ} (hΔ : 0 < Δ) (P : Program ℝ T M) (θ : ℝ → T → V)
    (k : ℤ) : apply (gridPullback t₀ Δ P) (fun k => θ (grid t₀ Δ k)) k =
      apply P θ (grid t₀ Δ k) := by
  funext j
  simp only [apply, foldAt_gridPullback hΔ]

end Pullback

section Const
variable [HasAct M V]

/-! ## Piecewise constancy -/

/-- **Piecewise constancy.** If `θ` is constant on an epoch of a span-only program
`P`, then so is `P ▷ θ`. -/
theorem apply_const_on_epoch {P : Program τ T M} (hP : SpanOnly P) {e : Span τ}
    (he : e ∈ epochs P) {θ : τ → T → V}
    (hθ : ∀ t t', e.mem t → e.mem t' → θ t = θ t')
    {t t' : τ} (ht : e.mem t) (ht' : e.mem t') : apply P θ t = apply P θ t' := by
  funext j
  simp only [apply, foldAt, effectsAt]
  rw [active_const_on_epoch hP he ht ht', hθ t t' ht ht']

end Const

end CategoricalInterventionsProofs
