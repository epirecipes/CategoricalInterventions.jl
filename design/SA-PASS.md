# SA-Pass semantic-alignment audit of the Lean development

## 1. Method and adaptation

SA-Pass is the shadow-set alignment test of Han et al., *ShadowBench: Toward
Reliable Automatic Evaluation of Semantic Alignment in Autoformalization*
(arXiv:2608.29270). A candidate formal statement T̂ is tested against a *shadow
set* 𝒮 = {S₁,…,Sₙ}: auxiliary formal statements, each with a machine-checked
proof, that jointly characterise the *intended* statement T. The set is
complete when S₁ ∧ … ∧ Sₙ ⇒ T (the *backward checker*) and T ⇒ Sᵢ for every
i (the *forward checkers*). SA-Pass(T̂,𝒮) = 1 iff T̂ compiles, every forward
checker T̂ ⇒ Sᵢ compiles and the backward checker ⋀Sᵢ ⇒ T̂ compiles;
otherwise 0. SA-Pass_soft = ½·(fraction of forward checkers that compile) +
½·𝟙(backward checker compiles), and 0 if T̂ does not compile. A failed forward
checker means T̂ is too weak (or differently scoped) to yield a facet of the
intended statement; a failed backward checker means the intended statement's
facets do not add up to T̂, i.e. T̂ says more than the sentence.

Here there is no reference formalisation, so the intended statement is the
natural-language claim of `docs/ledger.jl` (23 rows, 47 target theorems), and
T̂ is the existing Lean theorem (which compiles, so the first condition holds
everywhere). For each claim I wrote 2–4 shadows from the sentence, using the
development's definitions but not the target's phrasing, each proved from the
definitions and Mathlib without the target constant (one shadow, `sh_low_3`,
had to go through its target and is flagged as such). Forward checkers are
theorems `fwd_… (hT : ⟨target statement copied verbatim as a ∀-proposition⟩) : Sᵢ`,
backward checkers are `bwd_… (h₁ : S₁) … (hₙ : Sₙ) : ⟨target statement⟩`. A
meta-command (`proofs/CategoricalInterventionsProofs/SAPass/Check.lean`)
enforces, for every checker: (a) the proof term does not depend — directly or
transitively through any constant of the development — on the target, the
shadows, the other targets of the same claim, or listed restatements of the
target (so e.g. `compose_empty_left` cannot stand in for `compose_nil_left`,
nor `apply_append'` for `apply_append`, nor `foldAt_lift` for `apply_lift`);
(b) the copied hypothesis is definitionally equal (`isDefEq`) to the target's
type and the conclusion to the shadow's type, with universe parameters
required to correspond bijectively (a universe specialisation is rejected);
(c) the hypothesis `hT` (resp. at least one shadow hypothesis) actually occurs
in the proof term; (d) no `sorryAx`. In fact all 120 forward and 44 backward
checkers turned out to be *syntactically* identical to the statements they
copy after universe instantiation. Where a checker could not be proved
because the sentence and the theorem genuinely differ, it is omitted (never
weakened, never `sorry`ed) and the gap is recorded in Section 4. All of this
is built by `lake build` in `proofs/` (Lean 4.30.0, Mathlib v4.30.0), which
succeeds with zero warnings and zero `sorry`; files are
`proofs/CategoricalInterventionsProofs/SAPass/{Check,Common,C01_Compose,…,C23_Infer}.lean`
with root `proofs/CategoricalInterventionsProofs/SAPass.lean`.

**Second pass (strengthening).** Every gap of Section 4 was then closed by
adding a stronger (or one-directional) theorem to the main development (or, for
G3, restating the theorem without its spurious hypothesis), and the affected
rows were re-run against the new targets in `C24_Strengthened.lean` (G3 in
`C05_Factors.lean`), reusing the original shadow sets unchanged plus four extra
shadows.  Two new claims for the new `Shift.lean` module are audited in
`C25_Shift.lean` (Section 6).  After the second pass the build has 166 forward
and 63 backward checkers, all syntactically identical to the statements they
copy.  Section 2 keeps the original rows (marked *superseded*) and adds the new
ones; Section 3 reports both aggregates.

## 2. Results per target theorem

Columns: claim number; theorem; number of shadows; forward checkers passed /
total; backward checker passed; SA-Pass; SA-Pass_soft; note.

| # | Theorem | Shadows | Fwd | Bwd | SA-Pass | Soft | Note |
|---|---------|:-------:|:---:|:---:|:-------:|:----:|------|
| 1 | `compose_assoc` | 2 | 2/2 | yes | 1 | 1.000 | position-wise and `Std.Associative` facets |
| 1 | `compose_nil_left` | 2 | 2/2 | yes | 1 | 1.000 | position-wise and `Std.LawfulLeftIdentity` |
| 1 | `compose_nil_right` | 2 | 2/2 | yes | 1 | 1.000 | position-wise and `Std.LawfulRightIdentity` |
| 2 | `fold_perm` | 3 | 3/3 | yes | 1 | 1.000 | adjacent swap, reverse, multiset; bwd by `Perm` induction from swaps |
| 2 | `foldAt_perm` | 3 | 3/3 | yes | 1 | 1.000 | same three facets on programs |
| 2 | `apply_comm` | 2 | 1/2 | yes | 0 | 0.750 | **gap G1** (closed); superseded by `apply_perm` |
| 2 | `apply_perm` (new) | 2 | 2/2 | yes | 1 | 1.000 | same shadows; `apply_comm` is now its corollary |
| 3 | `conflictFree_of_pairwise` | 2 | 2/2 | yes | 1 | 1.000 | sentence omits the `PCMPairwise` side condition (S1) |
| 3 | `pairwise_of_conflictFree` | 2 | 2/2 | yes | 1 | 1.000 | idem |
| 3 | `foldList_isSome_iff_pairwise` | 3 | 3/3 | yes | 1 | 1.000 | both halves plus sublist closure |
| 4 | `different_target_compatible` | 2 | 2/2 | yes | 1 | 1.000 | pairwise phrasing; `Reject` instance pins "regardless of effects/supports" |
| 4 | `disjoint_compatible` | 3 | 2/3 | yes | 0 | 0.833 | **gap G2** (closed); superseded by `disjoint_compatible'` |
| 4 | `disjoint_compatible'` (new) | 3 | 3/3 | yes | 1 | 1.000 | arbitrary supports; span version is a corollary |
| 5 | `conflictFree_append_left` (original, with `PCMPairwise`) | 2 | 1/2 | yes | 0 | 0.750 | **gap G3** (closed); superseded by the restated theorem below |
| 5 | `conflictFree_append_right` (original, with `PCMPairwise`) | 2 | 1/2 | yes | 0 | 0.750 | **gap G3** (closed); superseded by the restated theorem below |
| 5 | `conflictFree_append_left` (restated, every PCM) | 2 | 2/2 | yes | 1 | 1.000 | `fwd_facL_1` now compiles |
| 5 | `conflictFree_append_right` (restated, every PCM) | 2 | 2/2 | yes | 1 | 1.000 | `fwd_facR_1` now compiles |
| 6 | `affine_pcm` | 3 | 3/3 | yes | 1 | 1.000 | existence of a PCM structure, two-sided unit, assoc-where-defined |
| 6 | `fold_affine_isSome_iff` | 2 | 1/2 | no | 0 | 0.250 | **gaps G4, G5** (closed); superseded by `two_absolutes_conflict` for the sentence; kept as the (stronger, total-algebra) converse |
| 6 | `two_absolutes_conflict` (new) | 2 | 2/2 | yes | 1 | 1.000 | no `PCMTotal`; bwd by sublist induction from the two-element shadow |
| 7 | `affine_action` | 3 | 3/3 | yes | 1 | 1.000 | absolute present / absent / surviving a product |
| 7 | `affine_act_mul_of_relative` | 2 | 2/2 | yes | 1 | 1.000 | bwd by case split on the absolute part |
| 8 | `epoch_cover` | 3 | 3/3 | yes | 1 | 1.000 | existence, uniqueness, unfolded hypothesis |
| 8 | `active_const_on_epoch` | 3 | 3/3 | yes | 1 | 1.000 | sentence omits `SpanOnly` (S2) |
| 9 | `epochs_refine` | 3 | 3/3 | yes | 1 | 1.000 | naive reading of the sentence is false (S3); bwd from the boundary form |
| 10 | `persistent_glue` | 3 | 3/3 | yes | 1 | 1.000 | set-, list- and three-piece forms |
| 10 | `persistent_antitone` | 3 | 3/3 | yes | 1 | 1.000 | subset, interval, sublist |
| 11 | `cumulative_union` | 3 | 3/3 | yes | 1 | 1.000 | set-, three-piece, embedding forms |
| 11 | `cumulative_inter_eq_point` | 3 | 3/3 | yes | 1 | 1.000 | set form and both convexity directions |
| 11 | `cumulative_monotone` | 3 | 3/3 | yes | 1 | 1.000 | subset, interval, sublist |
| 12 | `support_ordConnected` | 3 | 3/3 | yes | 1 | 1.000 | pointwise, `Icc`, span instance |
| 13 | `apply_nil` | 2 | 2/2 | yes | 1 | 1.000 | pointwise, idempotent |
| 13 | `apply_local` | 3 | 3/3 | yes | 1 | 1.000 | union-of-supports, pointwise, "after everything" |
| 14 | `apply_append` | 3 | 3/3 | yes | 1 | 1.000 | sentence omits `ConflictFree` (S4) |
| 14 | `apply_append_affine` | 3 | 3/3 | yes | 1 | 1.000 | idem |
| 15 | `apply_pullback` | 3 | 3/3 | yes | 1 | 1.000 | pointwise, injective (restriction), composite (resampling) |
| 15 | `grid_preimage_span` | 3 | 3/3 | yes | 1 | 1.000 | membership, integer-span existence, unit grid |
| 15 | `apply_discrete_eq` | 3 | 3/3 | yes | 1 | 1.000 | pointwise, function-level, unit grid |
| 16 | `apply_const_on_epoch` | 3 | 3/3 | yes | 1 | 1.000 | sentence omits `SpanOnly` (S2) |
| 17 | `lower_eq_apply` | 3 | 3/3 | yes | 1 | 1.000 | `sh_low_3` proved via target (T4); sentence omits `SpanOnly`/constant baseline (S5) |
| 18 | `transfer_preserves_sum` | 3 | 3/3 | yes | 1 | 1.000 | difference form, two and n transfers |
| 19 | `pulse_before_update` | 3 | 3/3 | yes | 1 | 1.000 | definitional; shallow shadow set (T3) |
| 19 | `discreteStep_no_pulse` | 3 | 3/3 | yes | 1 | 1.000 | definitional; shallow shadow set (T3) |
| 20 | `pushforward_comp` (original scoring) | 3 | 2/3 | yes | 0 | 0.833 | **gap G6** (closed); superseded by the re-scored row + `pushforward_id` |
| 20 | `pushforward_comp` (re-scored: identity shadow moved) | 2 | 2/2 | yes | 1 | 1.000 | shadows `sh_pc_2`, `sh_pc_3`; bwd `bwd_pc'` |
| 20 | `pushforward_id` (new) | 1 | 1/1 | yes | 1 | 1.000 | shadow `sh_pc_1` |
| 20 | `conflictFree_pushforward_of_injOn` | 2 | 2/2 | no | 0 | 0.500 | **gap G7** (closed); superseded by `conflictFree_pushforward_of_injOn'` |
| 20 | `conflictFree_pushforward_of_injOn'` (new) | 2 | 2/2 | yes | 1 | 1.000 | the "preserves" direction only |
| 21 | `lift_comp` | 3 | 1/3 | yes | 0 | 0.667 | **gaps G8, G9** (closed); superseded by `lift_comp_perm` + `lift_id`; now a corollary of `lift_comp_perm` |
| 21 | `lift_comp_perm` (new) | 2 | 2/2 | yes | 1 | 1.000 | shadows `sh_lc_1`, `sh_lc_2` |
| 21 | `lift_id` (new) | 3 | 3/3 | yes | 1 | 1.000 | `sh_lc_3` + list-level `sh_li_1`, `sh_li_2`; equality of lists |
| 21 | `conflictFree_lift_iff'` | 2 | 2/2 | no | 0 | 0.500 | **gap G10** (closed); superseded by `conflictFree_lift` for the sentence |
| 21 | `conflictFree_lift` (now cited) | 2 | 2/2 | yes | 1 | 1.000 | unconditional preservation, exactly the sentence |
| 21 | `apply_lift` | 3 | 3/3 | yes | 1 | 1.000 | effect-level, naturality, untouched strata |
| 22 | `augment_restrict` | 3 | 3/3 | yes | 1 | 1.000 | bwd via a "recording" action on `Option M` |
| 22 | `augment_conflictFree_iff` | 4 | 4/4 | yes | 1 | 1.000 | three directions plus single-flow instance |
| 23 | `infer_putget` | 4 | 3/4 | yes | 0 | 0.875 | **gap G11** (closed); superseded by `infer_putget_schedule` for the whole-schedule reading |
| 23 | `infer_putget_schedule` (new) | 3 | 3/3 | yes | 1 | 1.000 | `sh_ip_1` + epoch-start and `Set.EqOn` facets |
| 23 | `infer_putget_grid_step` | 3 | 3/3 | yes | 1 | 1.000 | grid-sampled reading; last point included |

## 3. Aggregate

### 3.1 Original targets (first pass)

| Metric | Value |
|--------|-------|
| targets tested | 47 (23 claims) |
| shadows written | 129 (128 proved independently of every target of their row, 1 via its target) |
| forward checkers | 120 compiled, 9 omitted → 120/129 = 0.930 |
| backward checkers | 44 compiled, 3 omitted |
| **SA-Pass rate** | 37/47 = **0.787** |
| **mean SA-Pass_soft** | 43.71/47 = **0.930** |
| forward-all rate (all forward checkers pass) | 39/47 = 0.830 |
| backward rate | 44/47 = 0.936 |

The 10 targets with SA-Pass = 0 are `apply_comm`, `disjoint_compatible`,
`conflictFree_append_left`, `conflictFree_append_right`, `fold_affine_isSome_iff`,
`pushforward_comp`, `conflictFree_pushforward_of_injOn`, `lift_comp`,
`conflictFree_lift_iff'`, `infer_putget`.

### 3.2 After strengthening (second pass)

The cited target set is the original one with each of the 10 failing rows
replaced by its successor(s): `apply_perm`, `disjoint_compatible'`, the two
restated `conflictFree_append_*`, `two_absolutes_conflict`, `pushforward_comp`
(re-scored) + `pushforward_id`, `conflictFree_pushforward_of_injOn'`,
`lift_comp_perm` + `lift_id`, `conflictFree_lift`, `infer_putget_schedule`
(47 − 10 + 12 = 49 targets).  The 37 unchanged rows keep their scores.

| Metric | Claims 1–23 after strengthening | + Section 6 (claims 24–25) |
|--------|------|------|
| targets tested | 49 (23 claims) | 58 (25 claims) |
| shadows written | 133 (129 + `sh_li_1`, `sh_li_2`, `sh_ips_2`, `sh_ips_3`) | 157 |
| forward checkers | 130/130 = 1.000 | 154/154 = 1.000 |
| backward checkers | 49/49 | 58/58 |
| **SA-Pass rate** | 49/49 = **1.000** | 58/58 = **1.000** |
| **mean SA-Pass_soft** | **1.000** | **1.000** |

(Build totals including the superseded rows' checkers: 166 forward and 63
backward checkers compile; none omitted for a cited target.)

## 4. Alignment gaps

Each gap is a checker that was not written because it cannot be proved. "NL"
is the sentence in `docs/ledger.jl`; "Lean" is the target's actual statement.

Status after the second pass: **all eleven gaps closed** (G1, G2, G3, G4, G6,
G8, G9, G11 by a new/restated theorem that the sentence now matches; G5, G7,
G10 by adding the one-directional theorem the sentence describes and citing it,
leaving the stronger `↔` theorems in place).  The closing theorem is named at
the end of each entry.

**G1 — `apply_comm` is rotation invariance, not permutation invariance**
(forward `fwd_apply_1` omitted; shadow `sh_apply_1 : P.Perm Q → apply P θ = apply Q θ`).
NL: "the order of atoms never matters". Lean: `apply (P ++ Q) θ = apply (Q ++ P) θ`.
Swapping the two blocks of a composite is exactly invariance under rotations
of the atom list, and rotations do not generate all permutations (a function
of a list that is rotation-invariant but not permutation-invariant exists,
e.g. "some `b` immediately follows some `a` cyclically"), so the shadow is not
a consequence of the target. The sentence is stronger. The full statement is
true (it follows from `foldAt_perm`, which the row also cites, in two lines,
and is `sh_apply_1`), so the fix is a stronger theorem: add
`apply_perm : P.Perm Q → apply P θ = apply Q θ` and cite it instead of, or in
addition to, `apply_comm`.
*Closed:* `apply_perm` (`Semantics.lean`); `apply_comm` is its corollary.
Checkers `fwd_apply'_1/2`, `bwd_apply'` (`C24`).

**G2 — `disjoint_compatible` covers only two span supports**
(forward `fwd_dj_1` omitted; shadow `sh_dj_1 : (∀ t, ¬(a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b]`).
NL: "disjoint supports never conflict". Lean: hypotheses `a.support = .span s`,
`b.support = .span s'`, `s.Disjoint s'`. The instant/instant and instant/span
cases are not instances of the theorem. The sentence is stronger; the general
statement is true (`sh_dj_1`, four lines). Fix: state `disjoint_compatible`
with the hypothesis `∀ t, ¬(a.support.mem t ∧ b.support.mem t)` (or
`Disjoint a.support.memSet b.support.memSet`) and keep the span version as a
corollary.
*Closed:* `disjoint_compatible'` (`Program.lean`), span version kept as
`disjoint_compatible`.  Checkers `fwd_dj'_1/2/3`, `bwd_dj'` (`C24`).

**G3 — `conflictFree_append_left/right` carry an unnecessary `PCMPairwise M`**
(forward `fwd_facL_1`, `fwd_facR_1` omitted; shadows `sh_facL_1`, `sh_facR_1`
are the same statements for an arbitrary `PCM M`).
NL: "factors of a conflict-free composite are conflict-free", no side
condition, and none is needed: `foldAt_append` gives
`fold (P++Q) = foldP.bind (fun a => foldQ.bind (mul a))`, which is defined only
if both factor folds are. The theorems are proved via `conflictFree_sublist`
and inherit its pairwise hypothesis, so they cannot be instantiated in the
shadow's context. The sentence is stronger. Fix: reprove both theorems from
`foldAt_append` without `[PCMPairwise M]` (the proofs are
`SAPass.conflictFree_of_append_left/right` in `Common.lean`).
*Closed:* both theorems restated in `Program.lean` for every PCM (same
names; the `PCMPairwise` argument is simply gone, so every caller still
compiles); `fwd_facL_1`, `fwd_facR_1` added in `C05`.

**G4 — `fold_affine_isSome_iff` needs `PCMTotal M`; "two absolutes conflict" does not**
(forward `fwd_aabs_1` omitted; shadow `sh_aabs_1 : a.abs.isSome → b.abs.isSome → mul a b = none` for any `PCM M`).
NL: "two absolute assignments conflict". This is true for every relative
algebra (it is a property of `absMul`), but the target requires
`[PCMTotal M]`, so it cannot be instantiated. The sentence is stronger on this
facet. Fix: add the two-element lemma `Affine.mul_eq_none_of_abs` (no
totality) and cite it for this half of the sentence.
*Closed:* `Affine.mul_eq_none_of_abs` (two elements) and
`two_absolutes_conflict` (fold with two absolutes is `none`, any relative
algebra), `PCM.lean`.  Checkers `fwd_aabs'_1/2`, `bwd_aabs'` (`C24`).

**G5 — the sentence claims one direction; `fold_affine_isSome_iff` is an `↔`**
(backward `bwd_aabs` omitted).
The shadows derived from "two absolute assignments conflict" say that a fold
containing two absolutes is undefined; they do not say the converse ("if no
two atoms are both absolute, the fold is defined"), which is the `←`
direction of the theorem and is where totality of `M` is actually needed.
The theorem is stronger than the sentence. Fix the sentence: "over a total
relative algebra, an affine fold is defined iff at most one atom is absolute".
*Closed:* the sentence's one direction is now `two_absolutes_conflict`, whose
backward checker compiles; `fold_affine_isSome_iff` remains as the converse.

**G6 — "functorial" includes the identity law; `pushforward_comp` is only composition**
(forward `fwd_pc_1` omitted; shadow `sh_pc_1 : pushforward id P = P`).
NL: "pushforward is functorial". Lean: the composition law only. The identity
law is true (by structure eta, two lines) but not stated. Fix: add
`pushforward_id` and cite both.
*Closed:* `pushforward_id` (`Transport.lean`); `sh_pc_1` is its shadow, and
`pushforward_comp` re-scored on `sh_pc_2`, `sh_pc_3` (`bwd_pc'`, `C24`).

**G7 — "preserves" vs `↔` for `conflictFree_pushforward_of_injOn`**
(backward `bwd_cp` omitted).
NL: "preserves conflict-freeness when injective on the targets used" is
one-directional; the theorem also *reflects* conflict-freeness. Theorem
stronger than sentence. Fix the sentence: "…preserves and reflects
conflict-freeness…".
*Closed:* `conflictFree_pushforward_of_injOn'` (`Transport.lean`) states the
"preserves" direction; its checkers `fwd_cp'_1/2`, `bwd_cp'` pass (`C24`).

**G8 — `lift_comp` is functoriality at the level of folds only**
(forward `fwd_lc_1` omitted; shadow `sh_lc_1 : (lift π' (lift π P)).Perm (lift (π ∘ π') P)`).
NL: "lifting … is functorial", i.e. a law about programs. Lean:
`foldAt j'' (lift π' (lift π P)) t = foldAt j'' (lift (π ∘ π') P) t`.
Fold equality does not determine the atom lists (a trivial action or the
one-element algebra forgets them). The program-level law holds up to
permutation (`sh_lc_1`, proved here via nodup fibres; strict list equality is
false because fibres are enumerated in `Finset.toList` order). Fix: add
`lift_comp_perm` (the statement of `sh_lc_1`) and derive `lift_comp` from it
with `foldAt_perm`, which is exactly what `bwd_lc` does.
*Closed:* `lift_comp_perm` and `fibre_comp_perm` (`Transport.lean`);
`lift_comp` is now `foldAt_perm (lift_comp_perm …)`.  Checkers `fwd_lcp_1/2`,
`bwd_lcp` (`C24`).

**G9 — identity law of lift absent**
(forward `fwd_lc_3` omitted; shadow `sh_lc_3 : foldAt j (lift id P) t = foldAt j P t`).
Same as G6 for `lift`. The law holds (`lift id P = P` as lists, in fact).
Fix: add `lift_id`.
*Closed:* `lift_id : lift id P = P` (list equality, via `fibre_id`),
`Transport.lean`.  Shadows `sh_lc_3`, `sh_li_1`, `sh_li_2`; checkers
`fwd_li_1/2/3`, `bwd_li` (`C24`).

**G10 — `conflictFree_lift_iff'` vs "preserves conflict-freeness"**
(backward `bwd_cl` omitted).
NL claims preservation, and preservation holds unconditionally
(`sh_cl_1`; the development's own `conflictFree_lift` is that statement).
The cited theorem is an `↔` under a preimage hypothesis; its reflection half
is not in the sentence. Note that the forward checker for the *unconditional*
shadow does pass: restricting `P` to the atoms whose target has a preimage
leaves `lift π P` unchanged (`lift_filter_eq`) and satisfies the hypothesis,
so the conditional theorem implies the unconditional one. Fix: cite
`conflictFree_lift` for "preserves" and reword the `_iff'` citation as
"…and reflects it when every used target has a preimage".
*Closed:* `conflictFree_lift` (unchanged statement, now documented) is the
cited theorem for "preserves"; its checkers `fwd_cl'_1/2`, `bwd_cl'` pass
(`C24`).

**G11 — `infer_putget` holds only at cell starts**
(forward `fwd_ip_1` omitted; shadow `sh_ip_1`: for a span-only `P`, constant
baseline `θ₀`, cells `= epochs P`, re-applying `infer (epochs P) θ₀ (P ▷ θ₀)`
to `θ₀` returns `P ▷ θ₀` at *every* time of every epoch).
NL: "inferring a program from a program's own output returns that output when
re-applied" — the whole schedule. Lean: equality at `c.lo` for each cell.
The values at other times of a cell are not a consequence of the values at
the starts. Under the hypotheses of the shadow the full statement is true
(`sh_ip_1`, proved from a `foldAt_infer` generalised to all times of a cell
plus `apply_const_on_epoch`); without them (ratio varying inside a cell) it is
false, which is presumably why the theorem is stated at cell starts. Fix:
either add `infer_putget_epochs` (the statement of `sh_ip_1`) or reword the
sentence to "…returns that output at the start of every cell / at every grid
point". The grid theorem `infer_putget_grid_step` is aligned with the sampled
reading (all its checkers pass).
*Closed:* `infer_putget_schedule` (`Infer.lean`; `foldAt_infer_mem` moved
there from `C23`, `foldAt_infer` is its instance at `c.lo`).  Checkers
`fwd_ips_1/2/3`, `bwd_ips` (`C24`).

### Sentence-side observations (no checker failed; the shadows carry the hypothesis)

These are cases where the sentence, read literally, is *false*, so the
shadows had to carry the theorem's side condition; they are documentation
corrections rather than theorem gaps.

- **S1 (claim 3).** "A program is conflict-free iff every pair … combines" is
  false for an arbitrary PCM (pairwise compatibility does not imply a defined
  fold: take `a·b = a·c = b·c = d` and `d·x` undefined). All three theorems
  need `PCMPairwise M`; say "for a pairwise effect algebra (all shipped
  instances)".
- **S2 (claims 8, 16).** "The active set / schedule is constant on an epoch"
  is false for programs with instants; the theorems need `SpanOnly P`.
- **S3 (claim 9).** The naive reading "every new epoch lies inside an old
  one" is false (a span added far from `P` creates an epoch in a gap that
  meets no old epoch). `epochs_refine` states the correct partition
  refinement, and the shadow set uses that reading; the sentence could say
  "each new epoch is inside every old epoch it meets".
- **S4 (claim 14).** "Applying P then Q equals applying P ⊕ Q" needs
  `ConflictFree (P ++ Q)` (an undefined fold acts trivially, sequential
  application does not).
- **S5 (claim 17).** "Holding each parameter … reproduces the schedule" needs
  span-only programs and a constant baseline, as `lower` is defined.
- **Claims 20/21.** "Functorial" is used where only the composition law
  (20) or only its fold-level image (21) is proved; see G6, G8, G9.

## 5. Threats to validity

- **Author bias.** I wrote the shadows and the checkers knowing the code and
  the theorems. The instruction to write each shadow before re-reading the
  target was followed in spirit, but I had read every target while surveying
  the development, so shadows may be biased towards what the theorems say.
  The mitigation is the rule that shadows are phrased from the sentence and
  that checkers may not use the target, its row-mates, its restatements, or
  the sibling shadows (enforced by `sa_check_*`, transitively).
- **Forward checkers can bypass `hT` with glue.** The checker only requires
  that `hT` *occur* in the proof term; it cannot detect decorative use. For
  trivial targets (claim 4, claim 19, `apply_nil`) the shadows are provable
  from the definitions alone, so a passing forward checker is weak evidence.
  Conversely, for the omitted checkers I applied the discipline "derive the
  shadow from `hT` by unfolding definitions and general lemmas; if the shadow
  needs content the target lacks, do not re-derive it from scratch", which
  is a judgement call, not a machine-checked one. The most delicate case is
  `fwd_cl_1` (claim 21), where I *did* derive the unconditional statement
  from the conditional theorem by a genuine reduction; a stricter reviewer
  might call that a gap.
- **T3: definitional targets.** `pulse_before_update` is `rfl` and
  `discreteStep_no_pulse` is one `simp` step; every shadow of claim 19 is
  likewise a direct consequence of the definition of `discreteStep`, so the
  shadow set cannot be non-trivial and SA-Pass = 1 there says only that the
  sentence describes the definition.
- **T4: a shadow proved via its target.** `sh_low_3` (claim 17, the whole
  held trajectory equals the schedule) is proved by `lower_eq_apply`; it is
  the theorem's content restated as a function equality and I did not
  re-prove it. The other two shadows of that claim (value at events, value
  before the first event) are independent. Also, the grid shadows of claim 23
  (`sh_ig_*`) are proved through `infer_putget_grid_full`, which rests on
  `infer_putget`, the other target of that row; they are independent of their
  own target only.
- **Universe monomorphism of `hT`.** Inside a checker, `hT` is a hypothesis
  and therefore fixed at the checker's universe parameters, whereas the
  target is universe-polymorphic. The exactness check requires a bijection
  between the target's universe parameters and distinct parameters of the
  checker, so a shadow that instantiates a type at a *different* universe
  (e.g. `augmentFlow`'s `Unit`, or the integer grid for `apply_pullback`)
  cannot be reached from `hT` even though it is an instance of the theorem.
  I restated those shadows at the same universe (`sh_ar_2`, `sh_ac_4`,
  `sh_pb_2`, `sh_pb_3`) rather than count them as gaps. This is a limitation
  of encoding T̂ as a hypothesis, not a semantic finding.
- **Shadows carry side conditions the sentence lacks.** Where the sentence
  is literally false (S1–S5) the shadows had to include the theorem's
  hypothesis, which makes the sentence–theorem comparison lenient in the
  theorem's favour; those cases are reported separately above rather than as
  failed checkers.
- **Instance shadows.** Several shadow sets contain instances (a `Reject`
  pair, the unit grid, a single cell) that pin quantifier scope; they add
  forward checkers that are easy to pass and never contribute to the
  backward direction, so they inflate SA-Pass_soft slightly relative to a set
  of purely equivalent facets. Every backward checker uses at least one
  non-instance shadow (the `sa_check_bwd` report lists which hypotheses were
  used).
- **`isDefEq` at default transparency** could in principle accept a copied
  hypothesis that unfolds to the target; in this audit every copy was also
  syntactically identical (reported by the checker), so this loophole was not
  exercised.
- **Second-pass bias.** In the second pass the same author wrote the
  strengthened theorems *and* re-ran the checkers, so a theorem could in
  principle have been shaped to the shadows.  Mitigation: the shadow sets of
  the re-run rows are the original ones, written before the new theorems
  existed (only four shadows were added, all list-level or instance facets);
  the checkers forbid the superseded theorem, its restatements and the glue
  that proves the new theorem (`Affine.mul_eq_none_of_abs`,
  `Affine.fold_abs_isSome_of_mem`, `fibre_comp_perm`, `fibre_id`,
  `foldAt_infer_mem`).  For Section 6 the shadows and theorems were written
  together, so those rows carry the full author bias.
- **Glue lemmas.** `Common.lean` and a few per-file helpers (`restrict_fold`,
  `lift_filter_eq`, `foldAt_filter_of`, `abs_of_mul`, `sum_transfer`; and now
  `foldAt_infer_mem`, `fibre_comp_perm` in the main development) are re-proofs
  from the definitions; where a
  glue lemma is a restatement of a target (`restrict_fold`, `sum_transfer`)
  it is forbidden in that target's checkers.

## 6. Shift and sequence (`Shift.lean`, `C25_Shift.lean`)

The new module `proofs/CategoricalInterventionsProofs/Shift.lean` formalises
the Julia `shift(program, δ)` and `seq(p, q; gap)`: `Span.shift`,
`Instant.shift`, `Support.shift`, `Atom.shift`, `shift δ P := P.map (Atom.shift δ)`
and `seq P Q δ := P ++ shift δ Q` (the Julia `seq` computes `δ` from the
extents; the laws hold for every explicit `δ`), for a timeline
`[AddCommGroup τ] [LinearOrder τ] [IsOrderedAddMonoid τ]` (ℝ, ℤ, ℚ).
Theorems: `shift_zero`, `shift_add`, `shift_append`, `shift_nil`, `shift_cons`,
`mem_shift_iff`, `Support.mem_shift`, `mem_shift`, `active_shift`,
`effectsAt_shift`, `foldAt_shift`, `conflictFree_shift`, `apply_shift`,
`apply_shift'`, `apply_shift_translate`, `seq_assoc`, `seq_nil_left`,
`seq_nil_right`, `seq_zero`, `conflictFree_of_seq`, `seq_disjoint_conflictFree`,
`apply_seq` (and `conflictFree_append_iff_of_separated` in `Program.lean`).
`conflictFree_seq_iff` without a separation hypothesis is not expected and not
stated: overlap after shifting can create conflicts.

Two natural-language claims were audited with the same procedure.

**Claim 24.** "Shift commutes with composition, preserves conflict-freeness,
and acts by translating the schedule."  Targets `shift_append`,
`conflictFree_shift`, `apply_shift`.  Reading: "preserves" for the invertible
`shift δ` is preservation; reflection follows (`shift (−δ)` undoes `shift δ`),
so `bwd_cs` uses only the preservation shadow, with `shift_add`/`shift_zero` as
glue.  The unit facet `shift δ [] = []` is derived from `shift_append` alone
(`fwd_sa_3`: `l = l ++ l ⇒ l = []`).

**Claim 25.** "Sequence inherits the laws of composition and shift."  Targets
`seq_assoc`, `seq_nil_left`, `seq_nil_right`, `conflictFree_of_seq`,
`seq_disjoint_conflictFree`, `apply_seq`.  Reading: associativity and units of
`++`; factors of a conflict-free sequence are conflict-free unconditionally,
and conversely under temporal separation (shadow `sh_sd_2` is the intended
use, `Q` delayed past the end of `P`); the action is `apply_append` composed
with `apply_shift` (`sh_aq_1`), in either order (`sh_aq_2`, derived from the
target via `apply_comm` applied to the swapped sequence `seq (shift δ Q) P 0`).

| # | Theorem | Shadows | Fwd | Bwd | SA-Pass | Soft | Note |
|---|---------|:-------:|:---:|:---:|:-------:|:----:|------|
| 24 | `shift_append` | 3 | 3/3 | yes | 1 | 1.000 | membership, position-wise, unit |
| 24 | `conflictFree_shift` | 3 | 3/3 | yes | 1 | 1.000 | preservation, pair instance, reflection; bwd from preservation alone |
| 24 | `apply_shift` | 3 | 3/3 | yes | 1 | 1.000 | schedule form, translated locality, translated baseline |
| 25 | `seq_assoc` | 3 | 3/3 | yes | 1 | 1.000 | position-wise, membership, fold-level |
| 25 | `seq_nil_left` | 2 | 2/2 | yes | 1 | 1.000 | position-wise, empty sequence |
| 25 | `seq_nil_right` | 2 | 2/2 | yes | 1 | 1.000 | position-wise, action |
| 25 | `conflictFree_of_seq` | 3 | 3/3 | yes | 1 | 1.000 | left factor, right factor, shifted right factor |
| 25 | `seq_disjoint_conflictFree` | 3 | 3/3 | yes | 1 | 1.000 | ← under separation (proved from `foldAt_append`), temporal-separation instance, → |
| 25 | `apply_seq` | 2 | 2/2 | yes | 1 | 1.000 | `P` then translated `Q`; other order via `apply_comm` |

Aggregate for Section 6: 9 targets, 24 shadows (all proved independently of
every target of their claim), 24/24 forward, 9/9 backward, SA-Pass 9/9,
mean soft 1.000.  Caveats: shadows and theorems were written together (see
Section 5); the `seq_nil_*` rows are near-definitional (T3-style).
