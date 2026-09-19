import CategoricalInterventionsProofs.Transport

/-!
# Augmentation: a flow becomes a parameter on a fresh target

A flow intervention on a Petri net adds a transition with a new rate parameter.
On the program side this is *augmentation*: extend the target space to
`T ⊕ T'`, keep `P` on the old targets, and place the new atoms on fresh ones.
The augmented program is conflict-free iff both parts are, and its folds on old
targets are those of `P`.
-/

namespace CategoricalInterventionsProofs

variable {τ T T' M : Type*} [LinearOrder τ] [DecidableEq T] [DecidableEq T'] [PCM M]

/-- Augment `P` (on `T`) by a program `Q` on fresh targets `T'`. -/
def augment (P : Program τ T M) (Q : Program τ T' M) : Program τ (T ⊕ T') M :=
  pushforward Sum.inl P ++ pushforward Sum.inr Q

/-- **Restriction.** On an old target the augmented fold is the original fold. -/
theorem augment_restrict (P : Program τ T M) (Q : Program τ T' M) (j : T) (t : τ) :
    foldAt (Sum.inl j) (augment P Q) t = foldAt j P t := by
  rw [augment, foldAt_append, foldAt_pushforward_of_injective Sum.inl_injective,
    foldAt_eq_one_of_none (Sum.inl j) (pushforward Sum.inr Q) t]
  · rcases foldAt j P t with _ | x <;> simp [mul_one]
  · intro b hb _ e
    obtain ⟨a, -, rfl⟩ := mem_pushforward.mp hb
    exact Sum.inr_ne_inl e

/-- On a fresh target the augmented fold is the fold of the new atoms. -/
theorem augment_fresh (P : Program τ T M) (Q : Program τ T' M) (j' : T') (t : τ) :
    foldAt (Sum.inr j') (augment P Q) t = foldAt j' Q t := by
  rw [augment, foldAt_append, foldAt_pushforward_of_injective Sum.inr_injective,
    foldAt_eq_one_of_none (Sum.inr j') (pushforward Sum.inl P) t]
  · rcases foldAt j' Q t with _ | x <;> simp [one_mul]
  · intro b hb _ e
    obtain ⟨a, -, rfl⟩ := mem_pushforward.mp hb
    exact Sum.inl_ne_inr e

/-- **Augmentation preserves conflict-freeness** iff the new atoms are conflict-free
among themselves. -/
theorem augment_conflictFree_iff (P : Program τ T M) (Q : Program τ T' M) :
    ConflictFree (augment P Q) ↔ ConflictFree P ∧ ConflictFree Q := by
  constructor
  · intro h
    refine ⟨fun t j => ?_, fun t j' => ?_⟩
    · rw [← augment_restrict P Q j t]; exact h t (Sum.inl j)
    · rw [← augment_fresh P Q j' t]; exact h t (Sum.inr j')
  · rintro ⟨hP, hQ⟩ t j
    rcases j with j | j'
    · rw [augment_restrict]; exact hP t j
    · rw [augment_fresh]; exact hQ t j'

/-- A flow intervention: a single atom (support `s`, effect `e`) on one fresh
rate-parameter target. -/
def augmentFlow (P : Program τ T M) (s : Support τ) (e : M) : Program τ (T ⊕ Unit) M :=
  augment P [⟨0, (), s, e⟩]

/-- A single atom never conflicts with itself. -/
theorem conflictFree_singleton (a : Atom τ T M) : ConflictFree [a] := by
  intro t j
  rw [foldAt_cons, foldAt_nil]
  split_ifs <;> simp [mul_one]

/-- Adding one flow preserves conflict-freeness exactly. -/
theorem augmentFlow_conflictFree_iff (P : Program τ T M) (s : Support τ) (e : M) :
    ConflictFree (augmentFlow P s e) ↔ ConflictFree P := by
  rw [augmentFlow, augment_conflictFree_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, conflictFree_singleton _⟩⟩

end CategoricalInterventionsProofs
