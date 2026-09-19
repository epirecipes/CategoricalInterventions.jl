/-!
# CategoricalInterventionsProofs

Lean 4 + Mathlib verification of the algebraic core of CategoricalInterventions.jl:
supports, effect algebras (partial commutative monoids), programs and
conflict-freeness, epochs, narratives, the action of programs on schedules,
transport along model morphisms, the lowering algorithm, augmentation, and
inference.  Lean verifies the algebra of programs, their action on schedules,
and the lowering algorithm; it does not verify the ODE solver or Catlab.

Every theorem below is fully proved, with no placeholder proofs.  Each line is
`name : statement in words`.

## `Support.lean`
* `span_lo_mem` : the start time of a span `[lo, hi)` belongs to it.
* `span_hi_not_mem` : the end time of a span does not belong to it.
* `overlaps_symm` : span overlap is symmetric.
* `disjoint_of_hi_le_lo` : if one span ends before the other starts they are disjoint.
* `overlaps_iff_exists_mem` : two spans overlap iff some time lies in both.
* `support_ordConnected` : every support (span or instant) is order-convex.
* `inter_span` : the intersection of two overlapping spans is a span.
* `start_mem`, `stop_not_mem`, `disjoint_of_stop_le_start`, `no_overlap_of_disjoint` :
  the v0.1 `ℕ`-interval results, as corollaries.

## `PCM.lean`
* `mul_one` : the unit is a right identity.
* `act_mul'` : a defined product acts in either order.
* `foldList_eq_foldl` : the fold equals the left fold used by the Julia code.
* `foldList_append` : the fold of a concatenation is the product of the folds.
* `fold_perm` : the fold is invariant under permutation (order irrelevance).
* `foldList_isSome_iff_pairwise` : for a `PCMPairwise` algebra, the fold is defined iff all pairs are compatible.
* `foldList_sublist` : definedness of the fold is inherited by sublists.
* `fold_pairwise_total` : for a total PCM the fold is always defined (and pairs are compatible).
* `fold_pairwise_reject` : pairwise suffices for `Reject`.
* `fold_pairwise_affine` : pairwise suffices for `Affine` over a total algebra.
* `fold_affine_isSome_iff` : an `Affine` fold is defined iff at most one element is absolute.
* `affine_pcm` : `Affine` is a commutative, associative partial monoid with unit `(none, 1)`.
* `affine_action` : the `Affine` action respects the unit and acts by the relative product on the absolute-or-value.
* `affine_act_mul_of_relative`, `affine_act_mul_of_relative'` : the one-sided action laws for `Affine`
  (sequential application agrees with the product when the later / earlier factor is purely relative).

## `Program.lean`
* `compose_assoc`, `compose_nil_left`, `compose_nil_right` : list append is a monoid on programs.
* `active_append` : the active set of `P ++ Q` is the concatenation of the active sets.
* `foldAt_append` : the fold of `P ++ Q` is the product of the folds.
* `foldAt_cons` : recursion for the fold.
* `foldAt_perm` : permuting a program does not change any fold.
* `foldAt_eq_one_of_none`, `foldAt_eq_one_of_not_active` : with nothing active the fold is the unit.
* `conflictFree_sublist` : sublists of conflict-free programs are conflict-free (pairwise PCMs).
* `conflictFree_append_left`, `conflictFree_append_right` : factors of a conflict-free composite are conflict-free.
* `conflictFree_of_pairwise`, `pairwise_of_conflictFree`, `conflictFree_iff_pairwise` :
  conflict-freeness is pairwise compatibility of active same-target atoms.
* `conflictFree_pair` : a two-atom program is conflict-free if the atoms are compatible whenever co-active on one target.
* `different_target_compatible` : two atoms on different targets never conflict.
* `disjoint_compatible` : two atoms on disjoint spans never conflict.

## `Epoch.lean`
* `mem_consecutiveSpans_of_sorted` : characterisation of consecutive spans of a sorted list.
* `consecutiveSpans_pairwise_disjoint` : consecutive spans of a sorted list are pairwise disjoint.
* `mem_epochs_iff` : an epoch is a span between two boundaries with no boundary strictly inside.
* `epochs_pairwise_disjoint` : epochs are pairwise disjoint.
* `epoch_cover` : every time inside some span lies in exactly one epoch.
* `active_const_on_epoch` : for a span-only program the active set is constant on each epoch.
* `epochs_refine` : an epoch of `P ++ Q` that meets an epoch of `P` is contained in it.
* `epochs_refine'` : each epoch of `P ++ Q` is contained in or disjoint from each epoch of `P`.

## `Narrative.lean`
* `persistent_antitone` : the persistent narrative is contravariant.
* `cumulative_monotone` : the cumulative narrative is covariant.
* `persistent_glue` : sheaf condition `A[a,b] = A[a,p] ∩ A[p,b]`.
* `cumulative_union` : cosheaf condition `C[a,b] = C[a,p] ∪ C[p,b]`.
* `cumulative_inter_eq_point` : cosheaf condition `C[a,p] ∩ C[p,b] = C[p,p]` (by convexity).
* `persistent_eq_active_of_point`, `cumulative_eq_active_of_point` : on a point both narratives are the active set.

## `Semantics.lean`
* `apply_nil` : identity: the empty program acts trivially.
* `apply_local` : locality: with nothing active at `t` the schedule is unchanged at `t`.
* `apply_append`, `apply_append'` : homomorphism: `(P ++ Q) ▷ θ = Q ▷ (P ▷ θ) = P ▷ (Q ▷ θ)` for acting PCMs.
* `apply_append_affine` : homomorphism for `Affine` when the later program is purely relative.
* `apply_comm` : `(P ++ Q) ▷ θ = (Q ++ P) ▷ θ` for every PCM.
* `apply_pullback` : naturality: `(P ▷ θ) ∘ r = (r^* P) ▷ (θ ∘ r)`.
* `gapply_toG` : the generalised semantics agrees with the ordinary one.
* `grid_preimage_span` : the preimage of `[a, b)` under `k ↦ t₀ + kΔ` is `[⌈(a−t₀)/Δ⌉, ⌈(b−t₀)/Δ⌉)`.
* `foldAt_gridPullback`, `apply_discrete_eq` : applying the grid pullback at `k` is applying `P` at `t₀ + kΔ`.
* `apply_const_on_epoch` : piecewise constancy: `P ▷ θ` is constant on each epoch when `θ` is.

## `Transport.lean`
* `pushforward_comp` : pushforward is functorial.
* `foldAt_pushforward_of`, `foldAt_pushforward_of_injective` : folds of a pushforward.
* `conflictFree_pushforward_of_injOn` : pushforward preserves and reflects conflict-freeness when `f` is injective on the used targets.
* `foldAt_copies`, `foldAt_lift` : the lifted fold at `j'` is the original fold at `π j'`.
* `lift_comp` : lift is functorial (at the level of folds).
* `conflictFree_lift_iff`, `conflictFree_lift` : lift preserves conflict-freeness and reflects it for surjective `π`.
* `apply_lift` : the lifted program acts fibrewise.

## `Lowering.lean`
* `holdLast_eq_default`, `holdLast_eq_of_max` : the hold-last callback returns the value of the greatest event `≤ t`.
* `active_eq_active_max` : the active set at `t` equals the active set at the greatest boundary `≤ t`.
* `lower_eq_apply` : lowering correctness: hold-last of the lowered events equals `P ▷ θ₀` at every time.
* `pulse_before_update` : the pre-update convention for pulses in discrete models.
* `discreteStep_no_pulse` : with no pulse the discrete step is the plain update.
* `transfer_preserves_sum` : a transfer between compartments conserves the total.

## `Augment.lean`
* `augment_restrict` : on an old target the augmented fold is the original fold.
* `augment_fresh` : on a fresh target the augmented fold is the new atoms' fold.
* `augment_conflictFree_iff` : augmentation is conflict-free iff both parts are.
* `conflictFree_singleton`, `augmentFlow_conflictFree_iff` : adding one flow preserves conflict-freeness exactly.

## `Infer.lean`
* `foldAt_infer` : at the start of a cell the inferred fold is the ratio `θ₁/θ₀`.
* `infer_putget` : put-get: applying the inferred program to `θ₀` gives `θ₁` at the start of every cell.
* `infer_putget_grid` : put-get on a sorted time grid.
-/

import CategoricalInterventionsProofs.Support
import CategoricalInterventionsProofs.PCM
import CategoricalInterventionsProofs.Program
import CategoricalInterventionsProofs.Epoch
import CategoricalInterventionsProofs.Narrative
import CategoricalInterventionsProofs.Semantics
import CategoricalInterventionsProofs.Transport
import CategoricalInterventionsProofs.Lowering
import CategoricalInterventionsProofs.Augment
import CategoricalInterventionsProofs.Infer
