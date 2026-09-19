import CategoricalInterventionsProofs.Program
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max

/-!
# Epochs

The *boundaries* of a program are the sorted, deduplicated endpoints of its
spans; its *epochs* are the half-open intervals between consecutive boundaries.
On each epoch the active set of a span-only program is constant, and the epochs
of a composite `P ++ Q` refine those of `P`.  Instants (pulses) are not part of
the epoch structure: they are handled separately as events in `Lowering.lean`.
-/

namespace CategoricalInterventionsProofs

variable {τ T M : Type*} [LinearOrder τ]

/-- The span endpoints of an atom (none for an instant). -/
def Atom.endpoints (a : Atom τ T M) : List τ :=
  match a.support with
  | .span s => [s.lo, s.hi]
  | .instant _ => []

theorem Atom.mem_endpoints {a : Atom τ T M} {b : τ} :
    b ∈ a.endpoints ↔ ∃ s : Span τ, a.support = .span s ∧ (b = s.lo ∨ b = s.hi) := by
  rcases h : a.support with s | i <;> simp [Atom.endpoints, h]

/-- All span endpoints of a program, with repetition. -/
def spanEndpoints (P : Program τ T M) : List τ := P.flatMap Atom.endpoints

/-- The set of span endpoints of a program. -/
def boundarySet (P : Program τ T M) : Finset τ := (spanEndpoints P).toFinset

theorem mem_boundarySet {P : Program τ T M} {b : τ} :
    b ∈ boundarySet P ↔ ∃ a ∈ P, ∃ s : Span τ, a.support = .span s ∧ (b = s.lo ∨ b = s.hi) := by
  simp [boundarySet, spanEndpoints, List.mem_flatMap, Atom.mem_endpoints]

/-- The sorted, deduplicated list of span endpoints. -/
def boundaries (P : Program τ T M) : List τ := (boundarySet P).sort (· ≤ ·)

theorem mem_boundaries {P : Program τ T M} {b : τ} :
    b ∈ boundaries P ↔ b ∈ boundarySet P :=
  Finset.mem_sort _

theorem boundaries_sorted (P : Program τ T M) : (boundaries P).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

theorem lo_mem_boundaries {P : Program τ T M} {a : Atom τ T M} {s : Span τ}
    (ha : a ∈ P) (hs : a.support = .span s) : s.lo ∈ boundaries P :=
  mem_boundaries.mpr (mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩)

theorem hi_mem_boundaries {P : Program τ T M} {a : Atom τ T M} {s : Span τ}
    (ha : a ∈ P) (hs : a.support = .span s) : s.hi ∈ boundaries P :=
  mem_boundaries.mpr (mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inr rfl⟩)

theorem boundaries_append_left {P Q : Program τ T M} {b : τ} (h : b ∈ boundaries P) :
    b ∈ boundaries (P ++ Q) := by
  rw [mem_boundaries, mem_boundarySet] at *
  obtain ⟨a, ha, s, hs, hb⟩ := h
  exact ⟨a, List.mem_append_left _ ha, s, hs, hb⟩

/-! ## Consecutive spans of a sorted list -/

/-- The spans between consecutive elements of a list (dropping degenerate pairs). -/
def consecutiveSpans : List τ → List (Span τ)
  | a :: b :: rest => (if h : a < b then [⟨a, b, h⟩] else []) ++ consecutiveSpans (b :: rest)
  | _ => []

@[simp] theorem consecutiveSpans_nil : consecutiveSpans ([] : List τ) = [] := rfl
@[simp] theorem consecutiveSpans_singleton (a : τ) : consecutiveSpans [a] = [] := rfl

theorem consecutiveSpans_cons_cons (a b : τ) (rest : List τ) (h : a < b) :
    consecutiveSpans (a :: b :: rest) = ⟨a, b, h⟩ :: consecutiveSpans (b :: rest) := by
  simp [consecutiveSpans, h]

theorem lo_mem_of_mem_consecutiveSpans {l : List τ} {s : Span τ}
    (h : s ∈ consecutiveSpans l) : s.lo ∈ l := by
  induction l with
  | nil => simp at h
  | cons a rest ih =>
    cases rest with
    | nil => simp at h
    | cons b rest' =>
      simp only [consecutiveSpans, List.mem_append] at h
      rcases h with h | h
      · split_ifs at h with hab
        · simp only [List.mem_singleton] at h
          subst h
          exact List.mem_cons_self
        · simp at h
      · exact List.mem_cons_of_mem _ (ih h)

theorem le_of_mem_sorted_cons {b c : τ} {l : List τ} (hl : (b :: l).Pairwise (· < ·))
    (hc : c ∈ b :: l) : b ≤ c := by
  rcases List.mem_cons.mp hc with rfl | hc
  · exact le_refl _
  · exact le_of_lt ((List.pairwise_cons.mp hl).1 c hc)

/-- Membership in the consecutive spans of a strictly sorted list: `s` is a
consecutive span iff both endpoints are in the list and no element lies
strictly between them. -/
theorem mem_consecutiveSpans_of_sorted {l : List τ} (hl : l.Pairwise (· < ·)) {s : Span τ} :
    s ∈ consecutiveSpans l ↔
      s.lo ∈ l ∧ s.hi ∈ l ∧ ∀ b ∈ l, ¬ (s.lo < b ∧ b < s.hi) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [consecutiveSpans_singleton, List.not_mem_nil, List.mem_singleton, false_iff]
      rintro ⟨h1, h2, -⟩
      exact lt_irrefl _ (h1 ▸ h2 ▸ s.lo_lt_hi)
    | cons b rest' =>
      have hl' : (b :: rest').Pairwise (· < ·) := hl.of_cons
      have ha_lt : ∀ c ∈ b :: rest', a < c := (List.pairwise_cons.mp hl).1
      have hab : a < b := ha_lt b List.mem_cons_self
      rw [consecutiveSpans_cons_cons a b rest' hab, List.mem_cons, ih hl']
      constructor
      · rintro (rfl | ⟨hlo, hhi, hbetween⟩)
        · refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
          intro c hc ⟨h1, h2⟩
          simp only at h1 h2
          rcases List.mem_cons.mp hc with rfl | hc
          · exact lt_irrefl _ h1
          · exact absurd h2 (not_lt.mpr (le_of_mem_sorted_cons hl' hc))
        · refine ⟨List.mem_cons_of_mem _ hlo, List.mem_cons_of_mem _ hhi, ?_⟩
          intro c hc hbc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact absurd hbc.1 (not_lt.mpr (le_of_lt (ha_lt _ hlo)))
          · exact hbetween c hc hbc
      · rintro ⟨hlo, hhi, hbetween⟩
        rcases List.mem_cons.mp hlo with hlo | hlo
        · left
          rcases List.mem_cons.mp hhi with hhi | hhi
          · exact absurd (hlo ▸ hhi ▸ s.lo_lt_hi) (lt_irrefl _)
          · have hb_le : b ≤ s.hi := le_of_mem_sorted_cons hl' hhi
            rcases eq_or_lt_of_le hb_le with heq | hlt
            · ext
              · exact hlo
              · exact heq.symm
            · exact absurd ⟨hlo ▸ hab, hlt⟩ (hbetween b (List.mem_cons_of_mem _ List.mem_cons_self))
        · right
          refine ⟨hlo, ?_, ?_⟩
          · rcases List.mem_cons.mp hhi with hhi | hhi
            · exact absurd (lt_trans (ha_lt _ hlo) s.lo_lt_hi) (hhi ▸ lt_irrefl _)
            · exact hhi
          · intro c hc hbc
            exact hbetween c (List.mem_cons_of_mem _ hc) hbc

/-- Consecutive spans of a strictly sorted list are pairwise disjoint. -/
theorem consecutiveSpans_pairwise_disjoint {l : List τ} (hl : l.Pairwise (· < ·)) :
    (consecutiveSpans l).Pairwise Span.Disjoint := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest' =>
      have hl' : (b :: rest').Pairwise (· < ·) := hl.of_cons
      have hab : a < b := (List.pairwise_cons.mp hl).1 b List.mem_cons_self
      rw [consecutiveSpans_cons_cons a b rest' hab, List.pairwise_cons]
      refine ⟨?_, ih hl'⟩
      intro s hs
      apply disjoint_of_hi_le_lo
      exact le_of_mem_sorted_cons hl' (lo_mem_of_mem_consecutiveSpans hs)

/-! ## Epochs -/

/-- The epochs of a program: the spans between consecutive boundaries. -/
def epochs (P : Program τ T M) : List (Span τ) := consecutiveSpans (boundaries P)

/-- An epoch is a span between two boundaries with no boundary strictly inside. -/
theorem mem_epochs_iff {P : Program τ T M} {e : Span τ} :
    e ∈ epochs P ↔
      e.lo ∈ boundaries P ∧ e.hi ∈ boundaries P ∧
        ∀ b ∈ boundaries P, ¬ (e.lo < b ∧ b < e.hi) :=
  mem_consecutiveSpans_of_sorted (boundaries_sorted P)

theorem epochs_pairwise_disjoint (P : Program τ T M) : (epochs P).Pairwise Span.Disjoint :=
  consecutiveSpans_pairwise_disjoint (boundaries_sorted P)

/-- A program is span-only when every atom's support is a span. -/
def SpanOnly (P : Program τ T M) : Prop := ∀ a ∈ P, ∃ s : Span τ, a.support = .span s

/-- `t` lies in the union of the spans of `P`. -/
def InSpanUnion (P : Program τ T M) (t : τ) : Prop :=
  ∃ a ∈ P, ∃ s : Span τ, a.support = .span s ∧ s.mem t

/-- **Epochs cover.** Every time inside some span of `P` lies in exactly one epoch. -/
theorem epoch_cover {P : Program τ T M} {t : τ} (h : InSpanUnion P t) :
    ∃! e : Span τ, e ∈ epochs P ∧ e.mem t := by
  obtain ⟨a, ha, s, hs, hlo, hhi⟩ := h
  have hlo_mem : s.lo ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩
  have hhi_mem : s.hi ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inr rfl⟩
  set L := (boundarySet P).filter (· ≤ t) with hL
  set U := (boundarySet P).filter (t < ·) with hU
  have hLne : L.Nonempty := ⟨s.lo, Finset.mem_filter.mpr ⟨hlo_mem, hlo⟩⟩
  have hUne : U.Nonempty := ⟨s.hi, Finset.mem_filter.mpr ⟨hhi_mem, hhi⟩⟩
  have hlo'_mem := Finset.max'_mem L hLne
  have hhi'_mem := Finset.min'_mem U hUne
  have hlo'_le : L.max' hLne ≤ t := (Finset.mem_filter.mp hlo'_mem).2
  have hlt_hi' : t < U.min' hUne := (Finset.mem_filter.mp hhi'_mem).2
  have hlo'B : L.max' hLne ∈ boundaries P :=
    mem_boundaries.mpr (Finset.mem_filter.mp hlo'_mem).1
  have hhi'B : U.min' hUne ∈ boundaries P :=
    mem_boundaries.mpr (Finset.mem_filter.mp hhi'_mem).1
  have hmaxL : ∀ b ∈ boundaries P, b ≤ t → b ≤ L.max' hLne := fun b hb hbt =>
    Finset.le_max' L b (Finset.mem_filter.mpr ⟨mem_boundaries.mp hb, hbt⟩)
  have hminU : ∀ b ∈ boundaries P, t < b → U.min' hUne ≤ b := fun b hb hbt =>
    Finset.min'_le U b (Finset.mem_filter.mpr ⟨mem_boundaries.mp hb, hbt⟩)
  refine ⟨⟨L.max' hLne, U.min' hUne, lt_of_le_of_lt hlo'_le hlt_hi'⟩,
    ⟨?_, ⟨hlo'_le, hlt_hi'⟩⟩, ?_⟩
  · rw [mem_epochs_iff]
    refine ⟨hlo'B, hhi'B, ?_⟩
    intro b hb ⟨h1, h2⟩
    simp only at h1 h2
    rcases le_or_gt b t with hbt | hbt
    · exact absurd (hmaxL b hb hbt) (not_le.mpr h1)
    · exact absurd (hminU b hb hbt) (not_le.mpr h2)
  · rintro e ⟨he, hlo_e, hhi_e⟩
    rw [mem_epochs_iff] at he
    obtain ⟨heloB, hehiB, hebetween⟩ := he
    have h1 : e.lo ≤ L.max' hLne := hmaxL e.lo heloB hlo_e
    have h2 : U.min' hUne ≤ e.hi := hminU e.hi hehiB hhi_e
    have h3 : L.max' hLne ≤ e.lo := by
      by_contra hc
      rw [not_le] at hc
      exact hebetween _ hlo'B ⟨hc, lt_of_le_of_lt hlo'_le hhi_e⟩
    have h4 : e.hi ≤ U.min' hUne := by
      by_contra hc
      rw [not_le] at hc
      exact hebetween _ hhi'B ⟨lt_of_le_of_lt hlo_e hlt_hi', hc⟩
    ext
    · exact le_antisymm h1 h3
    · exact le_antisymm h4 h2

/-- A span whose endpoints are boundaries contains an epoch time iff it contains
the whole epoch. -/
theorem span_mem_iff_of_epoch {P : Program τ T M} {e : Span τ} (he : e ∈ epochs P)
    {s : Span τ} (hlo : s.lo ∈ boundaries P) (hhi : s.hi ∈ boundaries P)
    {u : τ} (hu : e.mem u) : s.mem u ↔ s.lo ≤ e.lo ∧ e.hi ≤ s.hi := by
  rw [mem_epochs_iff] at he
  obtain ⟨-, -, hb⟩ := he
  obtain ⟨hu1, hu2⟩ := hu
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hc
      rw [not_le] at hc
      exact hb s.lo hlo ⟨hc, lt_of_le_of_lt h1 hu2⟩
    · by_contra hc
      rw [not_le] at hc
      exact hb s.hi hhi ⟨lt_of_le_of_lt hu1 h2, hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_trans h1 hu1, lt_of_lt_of_le hu2 h2⟩

/-- **Epoch constancy.** For a span-only program, the active set is the same at
any two times of one epoch. -/
theorem active_const_on_epoch {P : Program τ T M} (hP : SpanOnly P) {e : Span τ}
    (he : e ∈ epochs P) {t t' : τ} (ht : e.mem t) (ht' : e.mem t') :
    active P t = active P t' := by
  unfold active
  apply List.filter_congr
  intro a ha
  obtain ⟨s, hs⟩ := hP a ha
  rw [hs]
  simp only [Support.mem_span, decide_eq_decide]
  rw [span_mem_iff_of_epoch he (lo_mem_boundaries ha hs) (hi_mem_boundaries ha hs) ht,
    span_mem_iff_of_epoch he (lo_mem_boundaries ha hs) (hi_mem_boundaries ha hs) ht']

/-- **Refinement is functorial.** An epoch of `P ++ Q` that meets an epoch of `P`
is contained in it. -/
theorem epochs_refine {P Q : Program τ T M} {e' : Span τ} (he' : e' ∈ epochs (P ++ Q))
    {e : Span τ} (he : e ∈ epochs P) (hov : e'.overlaps e) : e'.memSet ⊆ e.memSet := by
  rw [mem_epochs_iff] at he he'
  obtain ⟨helo, hehi, -⟩ := he
  obtain ⟨-, -, hb'⟩ := he'
  obtain ⟨h1, h2⟩ := hov
  have hlo : e.lo ≤ e'.lo := by
    by_contra hc
    rw [not_le] at hc
    exact hb' e.lo (boundaries_append_left helo) ⟨hc, h2⟩
  have hhi : e'.hi ≤ e.hi := by
    by_contra hc
    rw [not_le] at hc
    exact hb' e.hi (boundaries_append_left hehi) ⟨h1, hc⟩
  exact Set.Ico_subset_Ico hlo hhi

/-- Every epoch of `P ++ Q` is either contained in or disjoint from each epoch of `P`. -/
theorem epochs_refine' {P Q : Program τ T M} {e' : Span τ} (he' : e' ∈ epochs (P ++ Q))
    {e : Span τ} (he : e ∈ epochs P) : e'.memSet ⊆ e.memSet ∨ e'.Disjoint e := by
  by_cases h : e'.overlaps e
  · exact Or.inl (epochs_refine he' he h)
  · exact Or.inr h

end CategoricalInterventionsProofs
