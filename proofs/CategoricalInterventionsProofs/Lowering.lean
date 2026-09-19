import CategoricalInterventionsProofs.Semantics
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Lowering to a callback

The events of a program are its span endpoints and instant times.  The
`PresetTimeCallback` lowering sets, at each event `e`, the parameters to
`P ▷ θ₀` evaluated at `e`, and the integrator then *holds* the value from the
last event.  We prove that this piecewise-constant trajectory equals `P ▷ θ₀`
at every time, for span-only programs with a constant baseline.

Also: the pre-update convention for pulses in discrete models, and conservation
of the total under a transfer between compartments.
-/

namespace CategoricalInterventionsProofs

open Finset

variable {τ T M V : Type*} [LinearOrder τ]

/-- The instant times of a program. -/
def instantTimes (P : Program τ T M) : List τ :=
  P.flatMap fun a => match a.support with
    | .instant i => [i.time]
    | .span _ => []

/-- The event set: span endpoints and instant times. -/
def eventSet (P : Program τ T M) : Finset τ := (spanEndpoints P ++ instantTimes P).toFinset

/-- The sorted, deduplicated events of a program. -/
def events (P : Program τ T M) : List τ := (eventSet P).sort (· ≤ ·)

theorem events_sorted (P : Program τ T M) : (events P).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

theorem mem_events {P : Program τ T M} {b : τ} : b ∈ events P ↔ b ∈ eventSet P :=
  Finset.mem_sort _

theorem instantTimes_eq_nil {P : Program τ T M} (hP : SpanOnly P) : instantTimes P = [] := by
  simp only [instantTimes, List.flatMap_eq_nil_iff]
  intro a ha
  obtain ⟨s, hs⟩ := hP a ha
  simp [hs]

theorem eventSet_eq_boundarySet {P : Program τ T M} (hP : SpanOnly P) :
    eventSet P = boundarySet P := by
  simp [eventSet, boundarySet, instantTimes_eq_nil hP]

/-- Hold the value from the last event at or before `t`, walking an ascending
event list; `d` is the value before the first event. -/
def holdLast : List (τ × V) → V → τ → V
  | [], d, _ => d
  | (s, v) :: rest, d, t => if s ≤ t then holdLast rest v t else d

theorem holdLast_eq_default {l : List (τ × V)} {t : τ} (h : ∀ e ∈ l, t < e.1) (d : V) :
    holdLast l d t = d := by
  cases l with
  | nil => rfl
  | cons e rest =>
    obtain ⟨s, v⟩ := e
    have : ¬ s ≤ t := not_le.mpr (h (s, v) List.mem_cons_self)
    simp [holdLast, this]

/-- On an ascending event list, `holdLast` returns the value of the greatest event
at or before `t`. -/
theorem holdLast_eq_of_max {l : List (τ × V)} (hs : l.Pairwise (fun a b => a.1 < b.1))
    {t : τ} {e : τ × V} (he : e ∈ l) (hle : e.1 ≤ t)
    (hmax : ∀ e' ∈ l, e'.1 ≤ t → e'.1 ≤ e.1) (d : V) : holdLast l d t = e.2 := by
  induction l generalizing d with
  | nil => simp at he
  | cons x rest ih =>
    obtain ⟨s, v⟩ := x
    have hrest : rest.Pairwise (fun a b => a.1 < b.1) := hs.of_cons
    have hlt : ∀ e' ∈ rest, s < e'.1 := (List.pairwise_cons.mp hs).1
    rcases List.mem_cons.mp he with rfl | he
    · simp only at hle
      simp only [holdLast, hle, if_true]
      apply holdLast_eq_default
      intro e' he'
      by_contra hc
      rw [not_lt] at hc
      exact absurd (hmax e' (List.mem_cons_of_mem _ he') hc) (not_le.mpr (hlt e' he'))
    · have hs_le : s ≤ t := le_trans (le_of_lt (hlt e he)) hle
      simp only [holdLast, hs_le, if_true]
      exact ih hrest he (fun e' he' h => hmax e' (List.mem_cons_of_mem _ he') h) v

section Lower
variable [DecidableEq T] [PCM M]

/-- The lowered event list for target `j`: at each event, the value of `P ▷ θ₀`. -/
def lower [HasAct M V] (P : Program τ T M) (θ0 : T → V) (j : T) : List (τ × V) :=
  (events P).map fun e => (e, apply P (fun _ => θ0) e j)

omit [DecidableEq T] [PCM M] in
/-- The active set at `t` equals the active set at the greatest boundary `≤ t`. -/
theorem active_eq_active_max {P : Program τ T M} (hP : SpanOnly P) {t e : τ} (hle : e ≤ t)
    (hmax : ∀ b ∈ boundarySet P, b ≤ t → b ≤ e) : active P t = active P e := by
  unfold active
  apply List.filter_congr
  intro a ha
  obtain ⟨s, hs⟩ := hP a ha
  rw [hs]
  simp only [Support.mem_span, decide_eq_decide, Span.mem]
  have hlo : s.lo ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩
  have hhi : s.hi ∈ boundarySet P := mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inr rfl⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hmax s.lo hlo h1, lt_of_le_of_lt hle h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨le_trans h1 hle, ?_⟩
    by_contra hc
    rw [not_lt] at hc
    exact absurd (hmax s.hi hhi hc) (not_le.mpr h2)

/-- **Lowering correctness.** For a span-only program and a constant baseline
`θ₀`, holding the value from the last event reproduces `P ▷ θ₀` at every time. -/
theorem lower_eq_apply [PCMAction M V] {P : Program τ T M} (hP : SpanOnly P) (θ0 : T → V)
    (j : T) (t : τ) :
    holdLast (lower P θ0 j) (θ0 j) t = apply P (fun _ => θ0) t j := by
  have hsorted : (lower P θ0 j).Pairwise (fun a b => a.1 < b.1) := by
    simp only [lower, List.pairwise_map]
    exact events_sorted P
  by_cases hex : ∃ b ∈ eventSet P, b ≤ t
  · set L := (eventSet P).filter (· ≤ t) with hL
    obtain ⟨b, hb, hbt⟩ := hex
    have hLne : L.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hbt⟩⟩
    have hmem := Finset.max'_mem L hLne
    have hle : L.max' hLne ≤ t := (Finset.mem_filter.mp hmem).2
    have hmemE : L.max' hLne ∈ eventSet P := (Finset.mem_filter.mp hmem).1
    have hmax : ∀ b ∈ eventSet P, b ≤ t → b ≤ L.max' hLne := fun b hb hbt =>
      Finset.le_max' L b (Finset.mem_filter.mpr ⟨hb, hbt⟩)
    rw [holdLast_eq_of_max hsorted (e := (L.max' hLne, apply P (fun _ => θ0) (L.max' hLne) j))]
    · simp only [apply, foldAt, effectsAt]
      rw [eventSet_eq_boundarySet hP] at hmax
      rw [active_eq_active_max hP hle hmax]
    · simp only [lower, List.mem_map]
      exact ⟨L.max' hLne, mem_events.mpr hmemE, rfl⟩
    · exact hle
    · intro e' he' hle'
      simp only [lower, List.mem_map] at he'
      obtain ⟨b', hb', rfl⟩ := he'
      exact hmax b' (mem_events.mp hb') hle'
  · push Not at hex
    rw [holdLast_eq_default]
    · symm
      rw [apply_local]
      intro a ha hm
      obtain ⟨s, hs⟩ := hP a ha
      rw [hs] at hm
      have : s.lo ∈ eventSet P := by
        rw [eventSet_eq_boundarySet hP]
        exact mem_boundarySet.mpr ⟨a, ha, s, hs, Or.inl rfl⟩
      exact absurd hm.1 (not_le.mpr (hex s.lo this))
    · intro e he
      simp only [lower, List.mem_map] at he
      obtain ⟨b, hb, rfl⟩ := he
      exact hex b (mem_events.mp hb)

end Lower

/-! ## Discrete models: pulses before the update -/

/-- One step of a discrete model with the pre-update convention: pulses at `t`
are applied to the state, then the update map. -/
def discreteStep {S : Type*} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ) : S :=
  upd (pulses t x) t

omit [LinearOrder τ] in
/-- **Pulse-before-update convention** (definitional). -/
theorem pulse_before_update {S : Type*} (upd : S → τ → S) (pulses : τ → S → S) (x : S)
    (t : τ) : discreteStep upd pulses x t = upd (pulses t x) t := rfl

omit [LinearOrder τ] in
/-- With no pulse at `t`, the step is the plain update. -/
theorem discreteStep_no_pulse {S : Type*} (upd : S → τ → S) (pulses : τ → S → S) (x : S)
    (t : τ) (h : pulses t = id) : discreteStep upd pulses x t = upd x t := by
  simp [discreteStep, h]

/-! ## Transfers conserve the total -/

section Transfer
variable {G : Type*} [AddCommGroup G] [Fintype T] [DecidableEq T]

/-- Move `n` units from compartment `src` to compartment `dst`. -/
def transfer (x : T → G) (src dst : T) (n : G) : T → G :=
  fun j => x j - (if j = src then n else 0) + (if j = dst then n else 0)

/-- **Transfers conserve the total.** -/
theorem transfer_preserves_sum (x : T → G) (src dst : T) (n : G) :
    ∑ j, transfer x src dst n j = ∑ j, x j := by
  simp [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

end Transfer

end CategoricalInterventionsProofs
