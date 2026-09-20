import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.Common

/-!
# SA-Pass claim 4

NL claim: **"Different targets never conflict; disjoint supports never conflict."**
Targets: `different_target_compatible`, `disjoint_compatible`.
-/

namespace CategoricalInterventionsProofs.SAPass.C04

open CategoricalInterventionsProofs

universe u v w

/-! ## Shadows for `different_target_compatible` -/

/-- NL: "different targets never conflict".  Facet: two atoms on different
targets are pairwise-compatible (the `O(n²)` check passes on them). -/
theorem sh_dt_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (a b : Atom τ T M) (h : a.target ≠ b.target) : PairwiseCompatible [a, b] := by
  rw [pairwiseCompatible_iff_combines]
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  unfold Combines
  intro hj _
  exact absurd hj h

/-- NL: "different targets never conflict" — regardless of supports and effects:
even two `Reject` effects (which never combine) with arbitrary supports are
conflict-free on different targets. -/
theorem sh_dt_2 {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
    (i₁ i₂ : ℕ) (j₁ j₂ : T) (S₁ S₂ : Support τ) (e₁ e₂ : E) (h : j₁ ≠ j₂) :
    ConflictFree [(⟨i₁, j₁, S₁, Reject.eff e₁⟩ : Atom τ T (Reject E)), ⟨i₂, j₂, S₂, Reject.eff e₂⟩] := by
  rw [conflictFree_pair_iff]
  intro t _ _ hj
  exact absurd hj h

sa_check_shadow_free sh_dt_1 [different_target_compatible, disjoint_compatible, conflictFree_pair]
sa_check_shadow_free sh_dt_2 [different_target_compatible, disjoint_compatible, conflictFree_pair]

theorem fwd_dt_1
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, a.target ≠ b.target → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M), a.target ≠ b.target → PairwiseCompatible [a, b] := by
  intro τ T M _ _ _ a b h
  rw [pairwiseCompatible_iff_combines, List.pairwise_iff_forall_sublist]
  intro x y hxy hj ⟨t, htx, hty⟩
  have hcf := (conflictFree_pair_iff a b).mp (hT h)
  -- the only two-element sublist of `[a, b]` is `[a, b]` itself
  have : x = a ∧ y = b := by
    have hl := hxy.length_le
    rcases List.sublist_cons_iff.mp hxy with h1 | ⟨r, hr, hr'⟩
    · have := h1.length_le; simp at this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
      rcases List.sublist_cons_iff.mp hr' with h2 | ⟨r', hr2, _⟩
      · have := h2.length_le; simp at this
      · obtain ⟨rfl, -⟩ := List.cons.inj hr2
        exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := this
  exact hcf t htx hty hj

sa_check_fwd fwd_dt_1 different_target_compatible sh_dt_1 forbid [disjoint_compatible, conflictFree_pair, sh_dt_2]

theorem fwd_dt_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, a.target ≠ b.target → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j₁ j₂ : T) (S₁ S₂ : Support τ) (e₁ e₂ : E), j₁ ≠ j₂ →
      ConflictFree [(⟨i₁, j₁, S₁, Reject.eff e₁⟩ : Atom τ T (Reject E)), ⟨i₂, j₂, S₂, Reject.eff e₂⟩] := by
  intro τ T E _ _ i₁ i₂ j₁ j₂ S₁ S₂ e₁ e₂ h
  exact hT h

sa_check_fwd fwd_dt_2 different_target_compatible sh_dt_2 forbid [disjoint_compatible, conflictFree_pair, sh_dt_1]

theorem bwd_dt
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M), a.target ≠ b.target → PairwiseCompatible [a, b])
    (h₂ : ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j₁ j₂ : T) (S₁ S₂ : Support τ) (e₁ e₂ : E), j₁ ≠ j₂ →
      ConflictFree [(⟨i₁, j₁, S₁, Reject.eff e₁⟩ : Atom τ T (Reject E)), ⟨i₂, j₂, S₂, Reject.eff e₂⟩]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M}, a.target ≠ b.target → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b h
  have _ := @h₂
  rw [conflictFree_pair_iff]
  intro t hta htb hj
  have hp := (pairwiseCompatible_iff_combines _).mp (h₁ a b h)
  exact (List.pairwise_cons.mp hp).1 b List.mem_cons_self hj ⟨t, hta, htb⟩

sa_check_bwd bwd_dt different_target_compatible [sh_dt_1, sh_dt_2] forbid [disjoint_compatible, conflictFree_pair]

/-! ## Shadows for `disjoint_compatible` -/

/-- NL: "disjoint supports never conflict" — for *any* two supports (spans or
instants) that share no time. -/
theorem sh_dj_1 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (a b : Atom τ T M) (h : ∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) :
    ConflictFree [a, b] := by
  rw [conflictFree_pair_iff]
  intro t hta htb _
  exact absurd ⟨hta, htb⟩ (h t)

/-- NL: "disjoint supports never conflict" — for spans, "disjoint" spelled out
as "one ends no later than the other starts". -/
theorem sh_dj_2 {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
    (a b : Atom τ T M) (s s' : Span τ) (ha : a.support = .span s) (hb : b.support = .span s')
    (h : s.hi ≤ s'.lo ∨ s'.hi ≤ s.lo) : ConflictFree [a, b] := by
  apply sh_dj_1
  intro t ⟨hta, htb⟩
  rw [ha] at hta
  rw [hb] at htb
  rcases h with h | h
  · exact absurd (lt_of_lt_of_le hta.2 (le_trans h htb.1)) (lt_irrefl t)
  · exact absurd (lt_of_lt_of_le htb.2 (le_trans h hta.1)) (lt_irrefl t)

/-- NL: "disjoint supports never conflict" — regardless of targets and effects:
two `Reject` effects on the *same* target with disjoint spans are conflict-free. -/
theorem sh_dj_3 {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
    (i₁ i₂ : ℕ) (j : T) (s s' : Span τ) (e₁ e₂ : E) (h : s.Disjoint s') :
    ConflictFree [(⟨i₁, j, .span s, Reject.eff e₁⟩ : Atom τ T (Reject E)),
      ⟨i₂, j, .span s', Reject.eff e₂⟩] := by
  apply sh_dj_1
  intro t ⟨hta, htb⟩
  exact h.not_mem hta htb

sa_check_shadow_free sh_dj_1 [different_target_compatible, disjoint_compatible, conflictFree_pair]
sa_check_shadow_free sh_dj_2 [different_target_compatible, disjoint_compatible, conflictFree_pair]
sa_check_shadow_free sh_dj_3 [different_target_compatible, disjoint_compatible, conflictFree_pair]

/- `fwd_dj_1` (disjoint_compatible ⇒ sh_dj_1) is OMITTED: the theorem is stated
only for two *span* supports (`a.support = .span s`, `b.support = .span s'`),
whereas the sentence covers every support; the cases instant/instant and
instant/span are not instances of the theorem.  See SA-PASS.md. -/

theorem fwd_dj_2
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M} {s s' : Span τ}, a.support = Support.span s →
      b.support = Support.span s' → s.Disjoint s' → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (s s' : Span τ), a.support = .span s → b.support = .span s' →
      s.hi ≤ s'.lo ∨ s'.hi ≤ s.lo → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b s s' ha hb h
  apply hT ha hb
  rcases h with h | h
  · exact disjoint_of_hi_le_lo h
  · intro hov
    exact disjoint_of_hi_le_lo h (overlaps_symm hov)

sa_check_fwd fwd_dj_2 disjoint_compatible sh_dj_2 forbid [different_target_compatible, conflictFree_pair, sh_dj_1, sh_dj_3]

theorem fwd_dj_3
    (hT : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M} {s s' : Span τ}, a.support = Support.span s →
      b.support = Support.span s' → s.Disjoint s' → ConflictFree [a, b]) :
    ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j : T) (s s' : Span τ) (e₁ e₂ : E), s.Disjoint s' →
      ConflictFree [(⟨i₁, j, .span s, Reject.eff e₁⟩ : Atom τ T (Reject E)),
        ⟨i₂, j, .span s', Reject.eff e₂⟩] := by
  intro τ T E _ _ i₁ i₂ j s s' e₁ e₂ h
  exact hT rfl rfl h

sa_check_fwd fwd_dj_3 disjoint_compatible sh_dj_3 forbid [different_target_compatible, conflictFree_pair, sh_dj_1, sh_dj_2]

theorem bwd_dj
    (h₁ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M), (∀ t, ¬ (a.support.mem t ∧ b.support.mem t)) → ConflictFree [a, b])
    (h₂ : ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      (a b : Atom τ T M) (s s' : Span τ), a.support = .span s → b.support = .span s' →
      s.hi ≤ s'.lo ∨ s'.hi ≤ s.lo → ConflictFree [a, b])
    (h₃ : ∀ {τ : Type u} {T : Type v} {E : Type w} [LinearOrder τ] [DecidableEq T]
      (i₁ i₂ : ℕ) (j : T) (s s' : Span τ) (e₁ e₂ : E), s.Disjoint s' →
      ConflictFree [(⟨i₁, j, .span s, Reject.eff e₁⟩ : Atom τ T (Reject E)),
        ⟨i₂, j, .span s', Reject.eff e₂⟩]) :
    ∀ {τ : Type u} {T : Type v} {M : Type w} [LinearOrder τ] [DecidableEq T] [PCM M]
      {a b : Atom τ T M} {s s' : Span τ}, a.support = Support.span s →
      b.support = Support.span s' → s.Disjoint s' → ConflictFree [a, b] := by
  intro τ T M _ _ _ a b s s' ha hb h
  have _ := @h₂
  have _ := @h₃
  apply h₁
  intro t ⟨hta, htb⟩
  rw [ha] at hta
  rw [hb] at htb
  exact h.not_mem hta htb

sa_check_bwd bwd_dj disjoint_compatible [sh_dj_1, sh_dj_2, sh_dj_3] forbid [different_target_compatible, conflictFree_pair]

end CategoricalInterventionsProofs.SAPass.C04
