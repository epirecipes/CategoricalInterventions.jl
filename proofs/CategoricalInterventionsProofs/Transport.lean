import CategoricalInterventionsProofs.Semantics
import Mathlib.Data.Fintype.Basic

/-!
# Transport along model morphisms

A *target map* `f : T → T'` induces a *pushforward* `f_* P` (rename targets);
a projection `π : T' → T` with finite fibres induces a *lift* `π^* P` (one copy
of each atom on every target in the fibre).  Pushforward preserves
conflict-freeness when `f` is injective on the targets `P` uses; lift preserves
it unconditionally (and reflects it when `π` is surjective), and the lifted
program acts fibrewise.
-/

namespace CategoricalInterventionsProofs

variable {τ T T' T'' M V : Type*} [LinearOrder τ]

/-- Rename each atom's target along `f`. -/
def pushforward (f : T → T') (P : Program τ T M) : Program τ T' M :=
  P.map fun a => ⟨a.id, f a.target, a.support, a.effect⟩

/-- The set of targets used by a program. -/
def targets (P : Program τ T M) : Set T := {j | ∃ a ∈ P, a.target = j}

/-- **Functoriality of pushforward.** -/
theorem pushforward_comp (f : T → T') (g : T' → T'') (P : Program τ T M) :
    pushforward g (pushforward f P) = pushforward (g ∘ f) P := by
  simp [pushforward, List.map_map, Function.comp_def]

@[simp] theorem pushforward_nil (f : T → T') : pushforward f ([] : Program τ T M) = [] := rfl

theorem pushforward_cons (f : T → T') (a : Atom τ T M) (P : Program τ T M) :
    pushforward f (a :: P) = ⟨a.id, f a.target, a.support, a.effect⟩ :: pushforward f P := rfl

theorem mem_pushforward {f : T → T'} {P : Program τ T M} {b : Atom τ T' M} :
    b ∈ pushforward f P ↔ ∃ a ∈ P, b = ⟨a.id, f a.target, a.support, a.effect⟩ := by
  simp only [pushforward, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

section Fold
variable [DecidableEq T] [DecidableEq T'] [PCM M]

/-- The fold of a pushforward at `f j` is the fold at `j`, provided no other
target of `P` is identified with `j` by `f`. -/
theorem foldAt_pushforward_of {f : T → T'} {P : Program τ T M} {j : T}
    (h : ∀ a ∈ P, f a.target = f j → a.target = j) (t : τ) :
    foldAt (f j) (pushforward f P) t = foldAt j P t := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    rw [pushforward_cons, foldAt_cons, foldAt_cons,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have : (f a.target = f j) ↔ (a.target = j) :=
      ⟨h a List.mem_cons_self, fun e => by rw [e]⟩
    simp only [this]

theorem foldAt_pushforward_of_injective {f : T → T'} (hf : Function.Injective f)
    (P : Program τ T M) (j : T) (t : τ) :
    foldAt (f j) (pushforward f P) t = foldAt j P t :=
  foldAt_pushforward_of (fun _ _ e => hf e) t

/-- **Pushforward preserves and reflects conflict-freeness** when `f` is injective
on the targets that `P` uses.  (If `f` merges two used targets, new conflicts can
appear; this is the honest statement of "transport can fail".) -/
theorem conflictFree_pushforward_of_injOn {f : T → T'} {P : Program τ T M}
    (hf : Set.InjOn f (targets P)) :
    ConflictFree (pushforward f P) ↔ ConflictFree P := by
  constructor
  · intro h t j
    by_cases hj : j ∈ targets P
    · rw [← foldAt_pushforward_of (f := f) (fun a ha e => hf ⟨a, ha, rfl⟩ hj e) t]
      exact h t (f j)
    · rw [foldAt_eq_one_of_none j P t (fun a ha _ e => hj ⟨a, ha, e⟩)]
      rfl
  · intro h t j'
    by_cases hj : ∃ a ∈ P, f a.target = j'
    · obtain ⟨a, ha, rfl⟩ := hj
      rw [foldAt_pushforward_of (f := f) (fun b hb e => hf ⟨b, hb, rfl⟩ ⟨a, ha, rfl⟩ e) t]
      exact h t a.target
    · push Not at hj
      rw [foldAt_eq_one_of_none j' (pushforward f P) t]
      · rfl
      · intro b hb _ e
        obtain ⟨a, ha, rfl⟩ := mem_pushforward.mp hb
        exact hj a ha e

end Fold

/-! ## Lift along a projection -/

section LiftDef
variable [DecidableEq T] [Fintype T']

/-- The fibre of `π` over `j`, as a list. -/
noncomputable def fibre (π : T' → T) (j : T) : List T' :=
  (Finset.univ.filter fun j' => π j' = j).toList

theorem mem_fibre {π : T' → T} {j : T} {j' : T'} : j' ∈ fibre π j ↔ π j' = j := by
  simp [fibre]

theorem fibre_nodup (π : T' → T) (j : T) : (fibre π j).Nodup := Finset.nodup_toList _

/-- Place a copy of an atom on each target of a list. -/
def copies (a : Atom τ T M) (L : List T') : Program τ T' M :=
  L.map fun j' => ⟨a.id, j', a.support, a.effect⟩

/-- Lift a program along `π`: one copy of each atom on every target in the fibre. -/
noncomputable def lift (π : T' → T) (P : Program τ T M) : Program τ T' M :=
  P.flatMap fun a => copies a (fibre π a.target)

@[simp] theorem lift_nil (π : T' → T) : lift π ([] : Program τ T M) = [] := rfl

theorem lift_cons (π : T' → T) (a : Atom τ T M) (P : Program τ T M) :
    lift π (a :: P) = copies a (fibre π a.target) ++ lift π P := by
  simp [lift, List.flatMap_cons]

end LiftDef

section Lift
variable [DecidableEq T] [DecidableEq T'] [Fintype T'] [PCM M]

omit [DecidableEq T] [Fintype T'] in
/-- The fold over the copies of one atom on a duplicate-free list of targets. -/
theorem foldAt_copies (a : Atom τ T M) {L : List T'} (hL : L.Nodup) (j' : T') (t : τ) :
    foldAt j' (copies a L) t =
      if a.support.mem t ∧ j' ∈ L then some a.effect else some one := by
  induction L with
  | nil => simp [copies]
  | cons x L ih =>
    have hx : x ∉ L := (List.nodup_cons.mp hL).1
    have ih := ih (List.nodup_cons.mp hL).2
    simp only [copies, List.map_cons] at ih ⊢
    rw [foldAt_cons, ih]
    by_cases hm : a.support.mem t
    · by_cases hj : x = j'
      · subst hj
        simp [hm, hx, mul_one]
      · have : j' ∈ x :: L ↔ j' ∈ L := by
          simp [List.mem_cons, Ne.symm hj]
        simp [hm, hj, this]
    · simp [hm]

/-- **Lift acts fibrewise.** The fold of `π^* P` at `j'` is the fold of `P` at `π j'`. -/
theorem foldAt_lift (π : T' → T) (P : Program τ T M) (j' : T') (t : τ) :
    foldAt j' (lift π P) t = foldAt (π j') P t := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    rw [lift_cons, foldAt_append, foldAt_copies a (fibre_nodup π a.target), ih, foldAt_cons]
    simp only [mem_fibre]
    have e : (a.target = π j') ↔ (π j' = a.target) := eq_comm
    simp only [e]
    by_cases hm : a.support.mem t
    · by_cases hj : π j' = a.target
      · simp [hm, hj]
      · simp [hm, hj, bind_mul_one]
    · simp [hm, bind_mul_one]

/-- **Functoriality of lift** (at the level of folds): lifting along `π` then `π'`
is lifting along `π ∘ π'`. -/
theorem lift_comp {T'' : Type*} [DecidableEq T''] [Fintype T'']
    (π : T' → T) (π' : T'' → T') (P : Program τ T M) (j'' : T'') (t : τ) :
    foldAt j'' (lift π' (lift π P)) t = foldAt j'' (lift (π ∘ π') P) t := by
  rw [foldAt_lift, foldAt_lift, foldAt_lift]
  rfl

/-- **Lift preserves conflict-freeness**, and reflects it when every target *used*
by `P` has a preimage under `π` (the condition the Julia `lift` checks). -/
theorem conflictFree_lift_iff' {π : T' → T} (P : Program τ T M)
    (hπ : ∀ j ∈ targets P, ∃ j', π j' = j) :
    ConflictFree (lift π P) ↔ ConflictFree P := by
  constructor
  · intro h t j
    by_cases hj : j ∈ targets P
    · obtain ⟨j', rfl⟩ := hπ j hj
      rw [← foldAt_lift π P j' t]
      exact h t j'
    · rw [foldAt_eq_one_of_none j P t (fun a ha _ e => hj ⟨a, ha, e⟩)]
      rfl
  · intro h t j'
    rw [foldAt_lift]
    exact h t (π j')

/-- Corollary: lift preserves and reflects conflict-freeness when `π` is surjective. -/
theorem conflictFree_lift_iff {π : T' → T} (hπ : Function.Surjective π) (P : Program τ T M) :
    ConflictFree (lift π P) ↔ ConflictFree P :=
  conflictFree_lift_iff' P (fun j _ => hπ j)

theorem conflictFree_lift {π : T' → T} {P : Program τ T M} (h : ConflictFree P) :
    ConflictFree (lift π P) := by
  intro t j'
  rw [foldAt_lift]
  exact h t (π j')

/-- **Lift acts fibrewise on schedules.** -/
theorem apply_lift [HasAct M V] (π : T' → T) (P : Program τ T M) (θ' : τ → T' → V)
    (t : τ) (j' : T') : apply (lift π P) θ' t j' = actOpt (foldAt (π j') P t) (θ' t j') := by
  simp [apply, foldAt_lift]

end Lift

end CategoricalInterventionsProofs
