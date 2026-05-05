import CategoricalInterventionsProofs.Interval

/-!
*Source: `Composition.lean`*

# Raw intervention program composition

The total core of `compose_interventions` is list append. The Julia function then
adds validation that may reject conflicting same-target overlaps. This file proves
the append-level monoid laws used by the Unicode `⊕` operator.

| # | Result | Status |
|---|--------|--------|
| 1 | Raw program composition is associative | ✅ |
| 2 | The empty program is a left identity | ✅ |
| 3 | The empty program is a right identity | ✅ |
-/

namespace CategoricalInterventionsProofs

inductive TargetKind where
  | parameter
  | state
  | process
  | observation
deriving DecidableEq, Repr

/-- A target is represented by a name and a target kind. -/
structure Target where
  name : Nat
  kind : TargetKind
deriving DecidableEq, Repr

/-- A simplified intervention atom. Effects are omitted because composition laws
only need atom identity, target, and interval support. -/
structure Atom where
  id : Nat
  target : Target
  support : Interval
deriving Repr

abbrev Program := List Atom

/-- Raw program composition before conflict validation. -/
def compose (p q : Program) : Program :=
  p ++ q

infixl:65 " ⊕ᵢ " => compose

theorem compose_assoc (p q r : Program) :
    (p ⊕ᵢ q) ⊕ᵢ r = p ⊕ᵢ (q ⊕ᵢ r) := by
  simp [compose, List.append_assoc]

theorem compose_empty_left (p : Program) :
    ([] : Program) ⊕ᵢ p = p := by
  simp [compose]

theorem compose_empty_right (p : Program) :
    p ⊕ᵢ ([] : Program) = p := by
  simp [compose]

end CategoricalInterventionsProofs
