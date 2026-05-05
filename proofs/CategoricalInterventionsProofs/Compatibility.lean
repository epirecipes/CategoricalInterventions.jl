import CategoricalInterventionsProofs.Composition

/-!
*Source: `Compatibility.lean`*

# Compatibility and conflicts

The Julia package rejects overlapping same-target interventions unless the target
declares an explicit combination algebra. In this simplified Lean model, a conflict
is exactly "same target and overlapping support". This file proves two important
safe cases.

| # | Result | Status |
|---|--------|--------|
| 1 | Different-target atoms are conflict-free | ✅ |
| 2 | Disjoint same-target atoms are conflict-free | ✅ |
-/

namespace CategoricalInterventionsProofs

def SameTarget (a b : Atom) : Prop :=
  a.target = b.target

def Conflicts (a b : Atom) : Prop :=
  SameTarget a b ∧ Overlaps a.support b.support

def Compatible (a b : Atom) : Prop :=
  ¬ Conflicts a b

theorem different_target_compatible {a b : Atom}
    (h : a.target ≠ b.target) : Compatible a b := by
  intro conflict
  exact h conflict.left

theorem disjoint_compatible {a b : Atom}
    (h : Disjoint a.support b.support) : Compatible a b := by
  intro conflict
  exact h conflict.right

end CategoricalInterventionsProofs
