import Lean

/-!
# SA-Pass checker commands

Meta-level support for the SA-Pass semantic-alignment procedure (Han et al.,
*ShadowBench: Toward Reliable Automatic Evaluation of Semantic Alignment in
Autoformalization*, arXiv:2608.29270), adapted to a development without a
reference formalisation.  For each natural-language claim we write *shadows*
`S₁ … Sₙ` (auxiliary formal statements with their own proofs), a *forward
checker* `fwd_i : T̂ → Sᵢ` for each shadow, and a *backward checker*
`bwd : S₁ → … → Sₙ → T̂`, where `T̂` is the statement of an existing target
theorem copied verbatim as a `∀`-proposition.

The commands below enforce that these checkers are honest:

* `sa_check_fwd chk tgt sh forbid [c₁, …]`
  - `chk`'s proof term must not use, directly or transitively through any
    constant of the `CategoricalInterventionsProofs` namespace, the target
    `tgt`, the shadow `sh`, or any listed `cᵢ` (the other targets of the same
    claim, the sibling shadows, and any development lemma that is a restatement
    of the target).  Transitivity is what stops `compose_empty_left` from
    standing in for `compose_nil_left`.
  - `chk`'s statement must be `∀ (hT : A), B` with `A` definitionally equal
    (`isDefEq`, default transparency) to the *type* of `tgt` and `B`
    definitionally equal to the type of `sh`.  So the copied hypothesis is the
    target statement exactly (not a weakening) and the conclusion is the
    shadow exactly (not a strengthening).
  - the bound variable `hT` must occur in the proof term.  This is a weak
    "the checker went through the target" test; it cannot tell essential use
    from decorative use.  (Universe parameters of the target/shadow are
    unified by fresh level metavariables, which must end up assigned to
    pairwise distinct universe parameters of the checker: a copy that
    specialises or identifies universes is rejected.)
  - the proof must not use `sorryAx`.

* `sa_check_bwd chk tgt [sh₁, …, shₙ] forbid [c₁, …]`
  - same independence test, with the shadows `shᵢ` and the target forbidden;
  - `chk`'s statement must be `∀ (h₁ : A₁) … (hₙ : Aₙ), B` with each `Aᵢ`
    definitionally equal to the type of `shᵢ` and `B` definitionally equal to
    the type of `tgt`;
  - the command reports which hypotheses `hᵢ` the proof term references.

* `sa_check_shadow_free sh [t₁, …]`
  - `sh` is a theorem whose proof term does not use, directly or transitively
    through the development, any of the targets `tᵢ` (nor `sorryAx`).

* `sa_check_shadow_via sh t`
  - the opposite assertion, for documentation: `sh`'s proof *does* depend on
    `t`.  Used when a shadow could only be proved through the target; the
    report lists these.

Every check either throws an error (failing `lake build`) or logs an
`info` line summarising what was verified.
-/

namespace CategoricalInterventionsProofs.SAPass

open Lean Elab Command Meta

/-- Constants under this prefix are recursed into when computing transitive
dependencies; nothing outside the development can depend on a target. -/
def devPrefix : Name := `CategoricalInterventionsProofs

/-- Transitive closure of the constants used by the values of the given roots,
recursing only through constants of the development. -/
partial def closure (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then closure env rest seen
    else
      let seen := seen.insert n
      let next : List Name :=
        if devPrefix.isPrefixOf n then
          match env.find? n with
          | some ci =>
            match ci.value? (allowOpaque := true) with
            | some v => v.getUsedConstants.toList
            | none => []
          | none => []
        else []
      closure env (next ++ rest) seen

/-- The transitive dependency set of a constant's proof term. -/
def depsOf (env : Environment) (n : Name) : CommandElabM NameSet := do
  let some ci := env.find? n | throwError "sa_check: unknown constant {n}"
  let some v := ci.value? (allowOpaque := true) | throwError "sa_check: {n} has no value (not a theorem?)"
  return closure env v.getUsedConstants.toList {}

/-- Fail if any forbidden constant (or `sorryAx`) is in the dependency set. -/
def assertFree (who : Name) (deps : NameSet) (forbidden : Array Name) : CommandElabM Unit := do
  if deps.contains ``sorryAx then
    throwError "sa_check: {who} depends on sorryAx"
  for f in forbidden do
    if deps.contains f then
      throwError "sa_check: {who} depends (directly or transitively) on forbidden constant {f}"

/-- The type of a constant with its universe parameters replaced by fresh level
metavariables, so that `isDefEq` can unify universes with the other side.
Returns the metavariables so that `assertLevelsExact` can inspect them. -/
def freshType (ci : ConstantInfo) : MetaM (Expr × List Level) := do
  let us ← mkFreshLevelMVars ci.levelParams.length
  return (ci.instantiateTypeLevelParams us, us)

/-- After unification, every fresh level metavariable must be assigned to a
universe *parameter* of the checker, and distinct metavariables to distinct
parameters.  Otherwise the checker's copy would be a universe specialisation
(or identification) of the statement rather than the statement itself. -/
def assertLevelsExact (who : MessageData) (us : List Level) : MetaM Unit := do
  let mut seen : Array Name := #[]
  for u in us do
    let u' ← instantiateLevelMVars u
    match u' with
    | .param n =>
      if seen.contains n then
        throwError "sa_check: {who}: two universe parameters of the statement were identified ({n}); the copy is a universe specialisation"
      seen := seen.push n
    | _ =>
      throwError "sa_check: {who}: a universe parameter of the statement was instantiated to `{u'}`; the copy must be universe-exact"

def resolveIds (ids : Array Ident) : CommandElabM (Array Name) :=
  ids.mapM fun i => resolveGlobalConstNoOverload i

syntax forbidList := " forbid " "[" ident,* "]"

def elabForbid : Option (TSyntax ``forbidList) → CommandElabM (Array Name)
  | none => pure #[]
  | some fb => match fb with
    | `(forbidList| forbid [$ids,*]) => resolveIds ids.getElems
    | _ => throwUnsupportedSyntax

/-- Names of the leading `∀`-binders of a type, up to `n`. -/
def leadingBinderNames : Expr → Nat → List Name
  | _, 0 => []
  | .forallE n _ b _, k + 1 => n :: leadingBinderNames b k
  | _, _ => []

syntax (name := saCheckFwd) "sa_check_fwd " ident ident ident (forbidList)? : command

@[command_elab saCheckFwd] def elabSaCheckFwd : CommandElab
  | `(sa_check_fwd $chk $tgt $sh $[$fb]?) => do
    let env ← getEnv
    let chkN ← resolveGlobalConstNoOverload chk
    let tgtN ← resolveGlobalConstNoOverload tgt
    let shN ← resolveGlobalConstNoOverload sh
    let forb ← elabForbid fb
    let some chkI := env.find? chkN | throwError "sa_check_fwd: unknown {chkN}"
    let some tgtI := env.find? tgtN | throwError "sa_check_fwd: unknown {tgtN}"
    let some shI := env.find? shN | throwError "sa_check_fwd: unknown {shN}"
    unless chkI matches .thmInfo _ do throwError "sa_check_fwd: {chkN} is not a theorem"
    -- (a) independence
    let deps ← depsOf env chkN
    assertFree chkN deps (#[tgtN, shN] ++ forb)
    -- (b) exactness of the copied hypothesis and of the conclusion, and use of hT
    let some v := chkI.value? (allowOpaque := true) | throwError "sa_check_fwd: no value"
    let (binderName, hTUsed, synBinder, synConcl) ← liftTermElabM do
      let chkT := chkI.type
      let (tT, tUs) ← freshType tgtI
      let (sT, sUs) ← freshType shI
      match chkT with
      | .forallE bn A _ _ =>
        unless ← isDefEq A tT do
          throwError "sa_check_fwd: the binder type of {chkN} is not definitionally equal to the type of {tgtN}:{indentExpr A}\nvs{indentExpr tT}"
        assertLevelsExact m!"{chkN} (hypothesis vs {tgtN})" tUs
        let synB := (← instantiateMVars A) == (← instantiateMVars tT)
        let (ok, synC, used) ← forallBoundedTelescope chkT (some 1) fun xs B => do
          let ok ← isDefEq B sT
          let synC := (← instantiateMVars B) == (← instantiateMVars sT)
          let body := v.beta xs
          let used := body.containsFVar xs[0]!.fvarId!
          pure (ok, synC, used)
        unless ok do
          throwError "sa_check_fwd: the conclusion of {chkN} is not definitionally equal to the type of {shN}"
        assertLevelsExact m!"{chkN} (conclusion vs {shN})" sUs
        pure (bn, used, synB, synC)
      | _ => throwError "sa_check_fwd: {chkN} must have the form ∀ (hT : target), shadow"
    unless hTUsed do
      throwError "sa_check_fwd: the proof of {chkN} does not reference its hypothesis {binderName}"
    logInfo m!"sa_check_fwd OK: {chkN} : {tgtN} ⇒ {shN}; independent of {(#[tgtN, shN] ++ forb).toList}; hypothesis{if synBinder then " syntactically" else " definitionally"} equal to target, conclusion{if synConcl then " syntactically" else " definitionally"} equal to shadow; {binderName} used"
  | _ => throwUnsupportedSyntax

syntax (name := saCheckBwd) "sa_check_bwd " ident ident "[" ident,* "]" (forbidList)? : command

@[command_elab saCheckBwd] def elabSaCheckBwd : CommandElab
  | `(sa_check_bwd $chk $tgt [$shs,*] $[$fb]?) => do
    let env ← getEnv
    let chkN ← resolveGlobalConstNoOverload chk
    let tgtN ← resolveGlobalConstNoOverload tgt
    let shNs ← resolveIds shs.getElems
    let forb ← elabForbid fb
    let some chkI := env.find? chkN | throwError "sa_check_bwd: unknown {chkN}"
    let some tgtI := env.find? tgtN | throwError "sa_check_bwd: unknown {tgtN}"
    unless chkI matches .thmInfo _ do throwError "sa_check_bwd: {chkN} is not a theorem"
    let shIs ← shNs.mapM fun n => do
      let some ci := env.find? n | throwError "sa_check_bwd: unknown {n}"
      pure ci
    -- (a) independence
    let deps ← depsOf env chkN
    assertFree chkN deps (#[tgtN] ++ shNs ++ forb)
    -- (b) exactness
    let some v := chkI.value? (allowOpaque := true) | throwError "sa_check_bwd: no value"
    let n := shNs.size
    let (usedNames, synAll) ← liftTermElabM do
      let chkT := chkI.type
      let (tT, tUs) ← freshType tgtI
      let names := leadingBinderNames chkT n
      unless names.length == n do
        throwError "sa_check_bwd: {chkN} must start with {n} hypothesis binders"
      forallBoundedTelescope chkT (some n) fun xs B => do
        let mut synAll := true
        for i in [0:n] do
          let (sT, sUs) ← freshType shIs[i]!
          let A ← inferType xs[i]!
          unless ← isDefEq A sT do
            throwError "sa_check_bwd: hypothesis {i+1} of {chkN} is not definitionally equal to the type of {shNs[i]!}:{indentExpr A}\nvs{indentExpr sT}"
          assertLevelsExact m!"{chkN} (hypothesis {i+1} vs {shNs[i]!})" sUs
          synAll := synAll && ((← instantiateMVars A) == (← instantiateMVars sT))
        unless ← isDefEq B tT do
          throwError "sa_check_bwd: the conclusion of {chkN} is not definitionally equal to the type of {tgtN}:{indentExpr B}\nvs{indentExpr tT}"
        assertLevelsExact m!"{chkN} (conclusion vs {tgtN})" tUs
        synAll := synAll && ((← instantiateMVars B) == (← instantiateMVars tT))
        let body := v.beta xs
        let mut used : List Name := []
        for i in [0:n] do
          if body.containsFVar xs[i]!.fvarId! then used := used ++ [shNs[i]!]
        pure (used, synAll)
    if usedNames.isEmpty then
      throwError "sa_check_bwd: the proof of {chkN} references none of its shadow hypotheses"
    logInfo m!"sa_check_bwd OK: {chkN} : {shNs.toList} ⇒ {tgtN}; independent of {(#[tgtN] ++ shNs ++ forb).toList}; statements {if synAll then "syntactically" else "definitionally"} equal; hypotheses used: {usedNames}"
  | _ => throwUnsupportedSyntax

syntax (name := saCheckShadowFree) "sa_check_shadow_free " ident "[" ident,* "]" : command

@[command_elab saCheckShadowFree] def elabSaCheckShadowFree : CommandElab
  | `(sa_check_shadow_free $sh [$tgts,*]) => do
    let env ← getEnv
    let shN ← resolveGlobalConstNoOverload sh
    let tgtNs ← resolveIds tgts.getElems
    let some shI := env.find? shN | throwError "sa_check_shadow_free: unknown {shN}"
    unless shI matches .thmInfo _ do throwError "sa_check_shadow_free: {shN} is not a theorem"
    let deps ← depsOf env shN
    assertFree shN deps tgtNs
    logInfo m!"sa_check_shadow_free OK: {shN} is proved independently of {tgtNs.toList}"
  | _ => throwUnsupportedSyntax

syntax (name := saCheckShadowVia) "sa_check_shadow_via " ident ident : command

@[command_elab saCheckShadowVia] def elabSaCheckShadowVia : CommandElab
  | `(sa_check_shadow_via $sh $tgt) => do
    let env ← getEnv
    let shN ← resolveGlobalConstNoOverload sh
    let tgtN ← resolveGlobalConstNoOverload tgt
    let some shI := env.find? shN | throwError "sa_check_shadow_via: unknown {shN}"
    unless shI matches .thmInfo _ do throwError "sa_check_shadow_via: {shN} is not a theorem"
    let deps ← depsOf env shN
    if deps.contains ``sorryAx then throwError "sa_check_shadow_via: {shN} depends on sorryAx"
    unless deps.contains tgtN do
      throwError "sa_check_shadow_via: {shN} does not actually depend on {tgtN}; use sa_check_shadow_free"
    logInfo m!"sa_check_shadow_via: {shN} is proved THROUGH the target {tgtN} (recorded in the report)"
  | _ => throwUnsupportedSyntax

end CategoricalInterventionsProofs.SAPass
