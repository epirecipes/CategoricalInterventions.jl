/-!
CategoricalInterventionsProofs: Lean 4 statements for the algebraic core of
CategoricalInterventions.jl.

The Julia package has richer runtime behavior, including conflict errors and
effect algebras. These Lean files formalize the small total fragment that sits
under the implementation:

* half-open intervals,
* raw program composition by list append,
* compatibility of different-target or disjoint same-target atoms.
-/

import CategoricalInterventionsProofs.Interval
import CategoricalInterventionsProofs.Composition
import CategoricalInterventionsProofs.Compatibility
