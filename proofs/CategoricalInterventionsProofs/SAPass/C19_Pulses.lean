import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.Lowering

/-!
# SA-Pass claim 19

NL claim: **"Discrete-time pulses are applied before the update."**
Targets: `pulse_before_update`, `discreteStep_no_pulse`.

Both targets are (essentially) definitional; every shadow below is likewise a
direct consequence of the definition of `discreteStep`, so the shadow set is
necessarily shallow (see the report).
-/

namespace CategoricalInterventionsProofs.SAPass.C19

open CategoricalInterventionsProofs

universe u v

/-! ## Shadows for `pulse_before_update` -/

/-- NL: "pulses are applied before the update" — the step *is* the update of the
pulsed state, as functions. -/
theorem sh_pu_1 {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) :
    discreteStep upd pulses = fun x t => upd (pulses t x) t := rfl

/-- NL facet: a pulse that resets the state to `y` makes the step update `y`. -/
theorem sh_pu_2 {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x y : S)
    (t : τ) (h : ∀ s, pulses t s = y) : discreteStep upd pulses x t = upd y t := by
  simp [discreteStep, h]

/-- NL facet: if the step differs from the plain update, the pulse changed the state. -/
theorem sh_pu_3 {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S)
    (t : τ) (h : discreteStep upd pulses x t ≠ upd x t) : pulses t x ≠ x := by
  intro hx
  apply h
  simp [discreteStep, hx]

sa_check_shadow_free sh_pu_1 [pulse_before_update, discreteStep_no_pulse]
sa_check_shadow_free sh_pu_2 [pulse_before_update, discreteStep_no_pulse]
sa_check_shadow_free sh_pu_3 [pulse_before_update, discreteStep_no_pulse]

theorem fwd_pu_1
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t = upd (pulses t x) t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S),
      discreteStep upd pulses = fun x t => upd (pulses t x) t := by
  intro τ S upd pulses
  funext x t
  exact hT upd pulses x t

sa_check_fwd fwd_pu_1 pulse_before_update sh_pu_1 forbid [discreteStep_no_pulse, sh_pu_2, sh_pu_3]

theorem fwd_pu_2
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t = upd (pulses t x) t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x y : S) (t : τ),
      (∀ s, pulses t s = y) → discreteStep upd pulses x t = upd y t := by
  intro τ S upd pulses x y t h
  rw [hT, h x]

sa_check_fwd fwd_pu_2 pulse_before_update sh_pu_2 forbid [discreteStep_no_pulse, sh_pu_1, sh_pu_3]

theorem fwd_pu_3
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t = upd (pulses t x) t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t ≠ upd x t → pulses t x ≠ x := by
  intro τ S upd pulses x t h hx
  apply h
  rw [hT, hx]

sa_check_fwd fwd_pu_3 pulse_before_update sh_pu_3 forbid [discreteStep_no_pulse, sh_pu_1, sh_pu_2]

theorem bwd_pu
    (h₁ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S),
      discreteStep upd pulses = fun x t => upd (pulses t x) t)
    (h₂ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x y : S) (t : τ),
      (∀ s, pulses t s = y) → discreteStep upd pulses x t = upd y t)
    (h₃ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t ≠ upd x t → pulses t x ≠ x) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      discreteStep upd pulses x t = upd (pulses t x) t := by
  intro τ S upd pulses x t
  have _ := @h₂
  have _ := @h₃
  exact congrFun (congrFun (h₁ upd pulses) x) t

sa_check_bwd bwd_pu pulse_before_update [sh_pu_1, sh_pu_2, sh_pu_3] forbid [discreteStep_no_pulse]

/-! ## Shadows for `discreteStep_no_pulse` -/

/-- NL: "with no pulse, the step is the plain update" — "no pulse at `t`" as
"the pulse map fixes every state". -/
theorem sh_np_1 {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S)
    (t : τ) (h : ∀ s, pulses t s = s) : discreteStep upd pulses x t = upd x t := by
  simp [discreteStep, h]

/-- NL facet: with no pulses at any time, every step is the plain update. -/
theorem sh_np_2 {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S)
    (t : τ) (h : pulses = fun _ => id) : discreteStep upd pulses x t = upd x t := by
  simp [discreteStep, h]

/-- NL facet: the identity pulse map gives the plain update. -/
theorem sh_np_3 {τ : Type u} {S : Type v} (upd : S → τ → S) (x : S) (t : τ) :
    discreteStep upd (fun _ => id) x t = upd x t := rfl

sa_check_shadow_free sh_np_1 [pulse_before_update, discreteStep_no_pulse]
sa_check_shadow_free sh_np_2 [pulse_before_update, discreteStep_no_pulse]
sa_check_shadow_free sh_np_3 [pulse_before_update, discreteStep_no_pulse]

theorem fwd_np_1
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses t = id → discreteStep upd pulses x t = upd x t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      (∀ s, pulses t s = s) → discreteStep upd pulses x t = upd x t := by
  intro τ S upd pulses x t h
  exact hT upd pulses x t (funext h)

sa_check_fwd fwd_np_1 discreteStep_no_pulse sh_np_1 forbid [pulse_before_update, sh_np_2, sh_np_3]

theorem fwd_np_2
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses t = id → discreteStep upd pulses x t = upd x t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses = (fun _ => id) → discreteStep upd pulses x t = upd x t := by
  intro τ S upd pulses x t h
  exact hT upd pulses x t (congrFun h t)

sa_check_fwd fwd_np_2 discreteStep_no_pulse sh_np_2 forbid [pulse_before_update, sh_np_1, sh_np_3]

theorem fwd_np_3
    (hT : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses t = id → discreteStep upd pulses x t = upd x t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (x : S) (t : τ),
      discreteStep upd (fun _ => id) x t = upd x t := by
  intro τ S upd x t
  exact hT upd (fun _ => id) x t rfl

sa_check_fwd fwd_np_3 discreteStep_no_pulse sh_np_3 forbid [pulse_before_update, sh_np_1, sh_np_2]

theorem bwd_np
    (h₁ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      (∀ s, pulses t s = s) → discreteStep upd pulses x t = upd x t)
    (h₂ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses = (fun _ => id) → discreteStep upd pulses x t = upd x t)
    (h₃ : ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (x : S) (t : τ),
      discreteStep upd (fun _ => id) x t = upd x t) :
    ∀ {τ : Type u} {S : Type v} (upd : S → τ → S) (pulses : τ → S → S) (x : S) (t : τ),
      pulses t = id → discreteStep upd pulses x t = upd x t := by
  intro τ S upd pulses x t h
  have _ := @h₂
  have _ := @h₃
  exact h₁ upd pulses x t (fun s => congrFun h s)

sa_check_bwd bwd_np discreteStep_no_pulse [sh_np_1, sh_np_2, sh_np_3] forbid [pulse_before_update]

end CategoricalInterventionsProofs.SAPass.C19
