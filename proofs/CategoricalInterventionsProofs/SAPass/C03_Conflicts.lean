import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.Common

/-!
# SA-Pass claim 3

NL claim: **"A program is conflict-free iff every pair of overlapping same-target
atoms combines."**
Targets: `conflictFree_of_pairwise`, `pairwise_of_conflictFree`,
`foldList_isSome_iff_pairwise`.

Note on scope: the sentence has no side condition, but the claim is false for an
arbitrary PCM (pairwise compatibility does not imply a defined fold), so every
shadow carries the `PCMPairwise M` hypothesis that the theorems carry.  The
sentence should say "for a pairwise effect algebra (all shipped instances)".
-/

namespace CategoricalInterventionsProofs.SAPass.C03

open CategoricalInterventionsProofs

universe u v w

/-! ## Shadows for `conflictFree_of_pairwise` ("if" direction) -/

/-- NL: "if every pair of overlapping same-target atoms combines, the program is
conflict-free" — stated with the pairwise relation spelled out on the program's
own atom list (not on per-time active sets). -/
theorem sh_cfp_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] [PCMPairwise M] (P : Program τ T M)
    (h : P.Pairwise (fun a b => a.target = b.target →
      (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome)) :
    ConflictFree P := by
  intro t j
  rw [foldAt, foldList_isSome_iff_pairwise, effectsAt, List.pairwise_map]
  exact (pairwiseCompatible_iff_combines P).mpr h t j

/-- NL facet: conflict-freeness is a two-atom property — if every two-atom
sub-program is conflict-free then so is the whole program. -/
theorem sh_cfp_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] [PCMPairwise M] (P : Program τ T M)
    (h : ∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b]) :
    ConflictFree P := by
  apply sh_cfp_1
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab hj ⟨t, hta, htb⟩
  exact (conflictFree_pair_iff a b).mp (h a b hab) t hta htb hj

sa_check_shadow_free sh_cfp_1 [conflictFree_of_pairwise, pairwise_of_conflictFree]
sa_check_shadow_free sh_cfp_2 [conflictFree_of_pairwise, pairwise_of_conflictFree]

theorem fwd_cfp_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, PairwiseCompatible P → ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M),
      P.Pairwise (fun a b => a.target = b.target →
        (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome) →
      ConflictFree P := by
  intro τ T M _ _ _ _ P h
  exact hT ((pairwiseCompatible_iff_combines P).mpr h)

sa_check_fwd fwd_cfp_1 conflictFree_of_pairwise sh_cfp_1
  forbid [pairwise_of_conflictFree, foldList_isSome_iff_pairwise, sh_cfp_2]

theorem fwd_cfp_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, PairwiseCompatible P → ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M),
      (∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b]) → ConflictFree P := by
  intro τ T M _ _ _ _ P h
  apply hT
  rw [pairwiseCompatible_iff_combines, List.pairwise_iff_forall_sublist]
  intro a b hab hj ⟨t, hta, htb⟩
  exact (conflictFree_pair_iff a b).mp (h a b hab) t hta htb hj

sa_check_fwd fwd_cfp_2 conflictFree_of_pairwise sh_cfp_2
  forbid [pairwise_of_conflictFree, foldList_isSome_iff_pairwise, sh_cfp_1]

theorem bwd_cfp
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M),
      P.Pairwise (fun a b => a.target = b.target →
        (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome) →
      ConflictFree P)
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M),
      (∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b]) → ConflictFree P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, PairwiseCompatible P → ConflictFree P := by
  intro τ T M _ _ _ _ P h
  have _ := @h₂
  exact h₁ P ((pairwiseCompatible_iff_combines P).mp h)

sa_check_bwd bwd_cfp conflictFree_of_pairwise [sh_cfp_1, sh_cfp_2]
  forbid [pairwise_of_conflictFree, foldList_isSome_iff_pairwise]

/-! ## Shadows for `pairwise_of_conflictFree` ("only if" direction) -/

/-- NL: "a conflict-free program has every pair of overlapping same-target atoms
combining" — pairwise relation spelled out on the atom list. -/
theorem sh_pcf_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] [PCMPairwise M] (P : Program τ T M) (h : ConflictFree P) :
    P.Pairwise (fun a b => a.target = b.target →
      (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome) := by
  have hp : PairwiseCompatible P := by
    intro t j
    have := h t j
    rwa [foldAt, foldList_isSome_iff_pairwise, effectsAt, List.pairwise_map] at this
  exact (pairwiseCompatible_iff_combines P).mp hp

/-- NL facet: every two-atom sub-program of a conflict-free program is conflict-free. -/
theorem sh_pcf_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T]
    [PCM M] [PCMPairwise M] (P : Program τ T M) (h : ConflictFree P) :
    ∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b] := by
  intro a b hab
  rw [conflictFree_pair_iff]
  intro t hta htb hj
  exact List.pairwise_iff_forall_sublist.mp (sh_pcf_1 P h) hab hj ⟨t, hta, htb⟩

sa_check_shadow_free sh_pcf_1 [conflictFree_of_pairwise, pairwise_of_conflictFree]
sa_check_shadow_free sh_pcf_2 [conflictFree_of_pairwise, pairwise_of_conflictFree]

theorem fwd_pcf_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, ConflictFree P → PairwiseCompatible P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M), ConflictFree P →
      P.Pairwise (fun a b => a.target = b.target →
        (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome) := by
  intro τ T M _ _ _ _ P h
  exact (pairwiseCompatible_iff_combines P).mp (hT h)

sa_check_fwd fwd_pcf_1 pairwise_of_conflictFree sh_pcf_1
  forbid [conflictFree_of_pairwise, foldList_isSome_iff_pairwise, sh_pcf_2]

theorem fwd_pcf_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, ConflictFree P → PairwiseCompatible P) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M), ConflictFree P →
      ∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b] := by
  intro τ T M _ _ _ _ P h a b hab
  rw [conflictFree_pair_iff]
  intro t hta htb hj
  have hp := (pairwiseCompatible_iff_combines P).mp (hT h)
  exact List.pairwise_iff_forall_sublist.mp hp hab hj ⟨t, hta, htb⟩

sa_check_fwd fwd_pcf_2 pairwise_of_conflictFree sh_pcf_2
  forbid [conflictFree_of_pairwise, foldList_isSome_iff_pairwise, sh_pcf_1]

theorem bwd_pcf
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M), ConflictFree P →
      P.Pairwise (fun a b => a.target = b.target →
        (∃ t, a.support.mem t ∧ b.support.mem t) → (mul a.effect b.effect).isSome))
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] (P : Program τ T M), ConflictFree P →
      ∀ a b : Atom τ T M, [a, b].Sublist P → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      [PCMPairwise M] {P : Program τ T M}, ConflictFree P → PairwiseCompatible P := by
  intro τ T M _ _ _ _ P h
  have _ := @h₂
  exact (pairwiseCompatible_iff_combines P).mpr (h₁ P h)

sa_check_bwd bwd_pcf pairwise_of_conflictFree [sh_pcf_1, sh_pcf_2]
  forbid [conflictFree_of_pairwise, foldList_isSome_iff_pairwise]

/-! ## Shadows for `foldList_isSome_iff_pairwise` (the effect-list level) -/

/-- NL: "the fold is defined iff every pair combines" — the "only if" half,
stated with pairs as two-element sublists. -/
theorem sh_fip_1 {M : Type u} [PCM M] [PCMPairwise M] (l : List M)
    (h : (foldList l).isSome) : ∀ a b : M, [a, b].Sublist l → (mul a b).isSome := by
  induction l with
  | nil => intro a b hab; simp at hab
  | cons m l ih =>
    intro a b hab
    rcases List.sublist_cons_iff.mp hab with hab | ⟨r, heq, hr⟩
    · exact ih (foldList_isSome_of_cons h) a b hab
    · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact PCMPairwise.compat_of_fold_cons a l h b (List.singleton_sublist.mp hr)

/-- NL: "the fold is defined iff every pair combines" — the "if" half. -/
theorem sh_fip_2 {M : Type u} [PCM M] [PCMPairwise M] (l : List M)
    (h : ∀ a b : M, [a, b].Sublist l → (mul a b).isSome) : (foldList l).isSome := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    apply PCMPairwise.fold_cons_of_compat m l
    · exact ih (fun a b hab => h a b (hab.trans (List.sublist_cons_self _ _)))
    · intro b hb
      exact h m b (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hb))

/-- NL facet: definedness of the fold is inherited by sublists ("dropping
effects never creates a conflict"). -/
theorem sh_fip_3 {M : Type u} [PCM M] [PCMPairwise M] {l₁ l₂ : List M} (h : l₁.Sublist l₂)
    (h₂ : (foldList l₂).isSome) : (foldList l₁).isSome :=
  sh_fip_2 l₁ (fun a b hab => sh_fip_1 l₂ h₂ a b (hab.trans h))

sa_check_shadow_free sh_fip_1 [foldList_isSome_iff_pairwise, conflictFree_of_pairwise, pairwise_of_conflictFree]
sa_check_shadow_free sh_fip_2 [foldList_isSome_iff_pairwise, conflictFree_of_pairwise, pairwise_of_conflictFree]
sa_check_shadow_free sh_fip_3 [foldList_isSome_iff_pairwise, conflictFree_of_pairwise, pairwise_of_conflictFree]

theorem fwd_fip_1
    (hT : ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome)) :
    ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome → ∀ a b : M, [a, b].Sublist l → (mul a b).isSome := by
  intro M _ _ l h a b hab
  exact List.pairwise_iff_forall_sublist.mp ((hT l).mp h) hab

sa_check_fwd fwd_fip_1 foldList_isSome_iff_pairwise sh_fip_1
  forbid [conflictFree_of_pairwise, pairwise_of_conflictFree, sh_fip_2, sh_fip_3]

theorem fwd_fip_2
    (hT : ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome)) :
    ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (∀ a b : M, [a, b].Sublist l → (mul a b).isSome) → (foldList l).isSome := by
  intro M _ _ l h
  exact (hT l).mpr (List.pairwise_iff_forall_sublist.mpr (fun {a b} hab => h a b hab))

sa_check_fwd fwd_fip_2 foldList_isSome_iff_pairwise sh_fip_2
  forbid [conflictFree_of_pairwise, pairwise_of_conflictFree, sh_fip_1, sh_fip_3]

theorem fwd_fip_3
    (hT : ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome)) :
    ∀ {M : Type u} [PCM M] [PCMPairwise M] {l₁ l₂ : List M}, l₁.Sublist l₂ →
      (foldList l₂).isSome → (foldList l₁).isSome := by
  intro M _ _ l₁ l₂ h h₂
  exact (hT l₁).mpr (((hT l₂).mp h₂).sublist h)

sa_check_fwd fwd_fip_3 foldList_isSome_iff_pairwise sh_fip_3
  forbid [conflictFree_of_pairwise, pairwise_of_conflictFree, sh_fip_1, sh_fip_2]

theorem bwd_fip
    (h₁ : ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome → ∀ a b : M, [a, b].Sublist l → (mul a b).isSome)
    (h₂ : ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (∀ a b : M, [a, b].Sublist l → (mul a b).isSome) → (foldList l).isSome)
    (h₃ : ∀ {M : Type u} [PCM M] [PCMPairwise M] {l₁ l₂ : List M}, l₁.Sublist l₂ →
      (foldList l₂).isSome → (foldList l₁).isSome) :
    ∀ {M : Type u} [PCM M] [PCMPairwise M] (l : List M),
      (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome) := by
  intro M _ _ l
  have _ := @h₃
  rw [List.pairwise_iff_forall_sublist]
  exact ⟨fun h a b hab => h₁ l h a b hab, fun h => h₂ l (fun a b hab => h hab)⟩

sa_check_bwd bwd_fip foldList_isSome_iff_pairwise [sh_fip_1, sh_fip_2, sh_fip_3]
  forbid [conflictFree_of_pairwise, pairwise_of_conflictFree]

end CategoricalInterventionsProofs.SAPass.C03
