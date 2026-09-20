import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.PCM

/-!
# SA-Pass claim 6

NL claim: **"Set-then-scale is a partial commutative monoid; two absolute
assignments conflict."**
Targets: `affine_pcm`, `fold_affine_isSome_iff`.
-/

namespace CategoricalInterventionsProofs.SAPass.C06

open CategoricalInterventionsProofs

universe u v

/-! ## Shadows for `affine_pcm` -/

/-- NL: "set-then-scale is a partial commutative monoid".  Facet: there is a PCM
structure on `Affine V M` whose product is `Affine.mul` and whose unit is
`(none, 1)`. -/
theorem sh_apcm_1 {V : Type u} {M : Type v} [PCM M] :
    ∃ inst : PCM (Affine V M), @PCM.mul _ inst = Affine.mul ∧ @PCM.one _ inst = ⟨none, PCM.one⟩ :=
  ⟨Affine.instPCM, rfl, rfl⟩

/-- NL facet: the unit `(none, 1)` is a *two-sided* identity for the product. -/
theorem sh_apcm_2 {V : Type u} {M : Type v} [PCM M] (a : Affine V M) :
    mul one a = some a ∧ mul a one = some a :=
  ⟨one_mul a, mul_one a⟩

/-- NL facet: associativity where defined — if `a·b` and `b·c` are both
defined then `(a·b)·c = a·(b·c)`. -/
theorem sh_apcm_3 {V : Type u} {M : Type v} [PCM M] (a b c ab bc : Affine V M)
    (hab : mul a b = some ab) (hbc : mul b c = some bc) : mul ab c = mul a bc := by
  have h := mul_assoc a b c
  rw [hab, hbc] at h
  simpa using h

sa_check_shadow_free sh_apcm_1 [affine_pcm, fold_affine_isSome_iff]
sa_check_shadow_free sh_apcm_2 [affine_pcm, fold_affine_isSome_iff]
sa_check_shadow_free sh_apcm_3 [affine_pcm, fold_affine_isSome_iff]

theorem fwd_apcm_1
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] (a b c : Affine V M),
      mul a b = mul b a ∧ mul one a = some a ∧
      (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc)) :
    ∀ {V : Type u} {M : Type v} [PCM M],
      ∃ inst : PCM (Affine V M), @PCM.mul _ inst = Affine.mul ∧ @PCM.one _ inst = ⟨none, PCM.one⟩ := by
  intro V M _
  refine ⟨⟨⟨none, PCM.one⟩, Affine.mul, fun a b => (hT a b a).1, fun a => (hT a a a).2.1,
    fun a b c => (hT a b c).2.2⟩, rfl, rfl⟩

sa_check_fwd fwd_apcm_1 affine_pcm sh_apcm_1 forbid [fold_affine_isSome_iff, sh_apcm_2, sh_apcm_3]

theorem fwd_apcm_2
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] (a b c : Affine V M),
      mul a b = mul b a ∧ mul one a = some a ∧
      (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc)) :
    ∀ {V : Type u} {M : Type v} [PCM M] (a : Affine V M),
      mul one a = some a ∧ mul a one = some a := by
  intro V M _ a
  refine ⟨(hT a a a).2.1, ?_⟩
  rw [(hT a one a).1]
  exact (hT a a a).2.1

sa_check_fwd fwd_apcm_2 affine_pcm sh_apcm_2 forbid [fold_affine_isSome_iff, sh_apcm_1, sh_apcm_3]

theorem fwd_apcm_3
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] (a b c : Affine V M),
      mul a b = mul b a ∧ mul one a = some a ∧
      (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc)) :
    ∀ {V : Type u} {M : Type v} [PCM M] (a b c ab bc : Affine V M),
      mul a b = some ab → mul b c = some bc → mul ab c = mul a bc := by
  intro V M _ a b c ab bc hab hbc
  have h := (hT a b c).2.2
  rw [hab, hbc] at h
  simpa using h

sa_check_fwd fwd_apcm_3 affine_pcm sh_apcm_3 forbid [fold_affine_isSome_iff, sh_apcm_1, sh_apcm_2]

theorem bwd_apcm
    (h₁ : ∀ {V : Type u} {M : Type v} [PCM M],
      ∃ inst : PCM (Affine V M), @PCM.mul _ inst = Affine.mul ∧ @PCM.one _ inst = ⟨none, PCM.one⟩)
    (h₂ : ∀ {V : Type u} {M : Type v} [PCM M] (a : Affine V M),
      mul one a = some a ∧ mul a one = some a)
    (h₃ : ∀ {V : Type u} {M : Type v} [PCM M] (a b c ab bc : Affine V M),
      mul a b = some ab → mul b c = some bc → mul ab c = mul a bc) :
    ∀ {V : Type u} {M : Type v} [PCM M] (a b c : Affine V M),
      mul a b = mul b a ∧ mul one a = some a ∧
      (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc) := by
  intro V M _ a b c
  have _ := @h₃
  obtain ⟨inst, hmul, -⟩ := @h₁ V M _
  refine ⟨?_, (h₂ a).1, ?_⟩
  · have := inst.mul_comm a b
    rw [hmul] at this
    exact this
  · have := inst.mul_assoc a b c
    rw [hmul] at this
    exact this

sa_check_bwd bwd_apcm affine_pcm [sh_apcm_1, sh_apcm_2, sh_apcm_3] forbid [fold_affine_isSome_iff]

/-! ## Shadows for `fold_affine_isSome_iff` -/

/-- NL: "two absolute assignments conflict" — for *any* relative algebra `M`
(the product of two absolutes is undefined whatever the relative parts are). -/
theorem sh_aabs_1 {V : Type u} {M : Type v} [PCM M] (a b : Affine V M)
    (ha : a.abs.isSome) (hb : b.abs.isSome) : mul a b = none := by
  obtain ⟨xa, ma⟩ := a
  obtain ⟨xb, mb⟩ := b
  cases xa <;> cases xb <;> simp_all [Affine.mul_mk]

/-- NL: "two absolute assignments conflict" — at the level of folds (over a total
relative algebra, where the theorem lives): a list containing two absolutes has
an undefined fold. -/
theorem sh_aabs_2 {V : Type u} {M : Type v} [PCM M] [PCMTotal M] (l : List (Affine V M))
    (a b : Affine V M) (hab : [a, b].Sublist l) (ha : a.abs.isSome) (hb : b.abs.isSome) :
    foldList l = none := by
  by_contra hne
  have hs : (foldList l).isSome := Option.ne_none_iff_isSome.mp hne
  rw [fold_pairwise_affine] at hs
  have := List.pairwise_iff_forall_sublist.mp hs hab
  rw [sh_aabs_1 a b ha hb] at this
  simp at this

sa_check_shadow_free sh_aabs_1 [affine_pcm, fold_affine_isSome_iff]
sa_check_shadow_free sh_aabs_2 [affine_pcm, fold_affine_isSome_iff]

/- `fwd_aabs_1` (fold_affine_isSome_iff ⇒ sh_aabs_1) is OMITTED: the shadow is
stated for every relative algebra `M`; the target requires a `PCMTotal M`
instance, which is not available.  See SA-PASS.md. -/

theorem fwd_aabs_2
    (hT : ∀ {V : Type u} {M : Type v} [PCM M] [PCMTotal M] (l : List (Affine V M)),
      (foldList l).isSome ↔ l.Pairwise (fun a b => ¬ (a.abs.isSome ∧ b.abs.isSome))) :
    ∀ {V : Type u} {M : Type v} [PCM M] [PCMTotal M] (l : List (Affine V M)) (a b : Affine V M),
      [a, b].Sublist l → a.abs.isSome → b.abs.isSome → foldList l = none := by
  intro V M _ _ l a b hab ha hb
  by_contra hne
  have hs : (foldList l).isSome := Option.ne_none_iff_isSome.mp hne
  rw [hT] at hs
  exact List.pairwise_iff_forall_sublist.mp hs hab ⟨ha, hb⟩

sa_check_fwd fwd_aabs_2 fold_affine_isSome_iff sh_aabs_2 forbid [affine_pcm, sh_aabs_1, fold_pairwise_affine]

/- `bwd_aabs` is OMITTED: the sentence claims only that two absolutes conflict;
it does not claim the converse ("if no two atoms are both absolute, the fold is
defined"), which is the `←` direction of the theorem and needs totality of `M`.
The shadow set derived from the sentence therefore cannot imply the theorem.
See SA-PASS.md. -/

end CategoricalInterventionsProofs.SAPass.C06
