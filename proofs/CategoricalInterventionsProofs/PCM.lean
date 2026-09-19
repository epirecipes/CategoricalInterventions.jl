import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Cases

/-!
# Partial commutative monoids and their actions

An *effect algebra* on a target is a partial commutative monoid (PCM): a unit,
and a partial product `mul : M → M → Option M` that is commutative and
associative (in Kleisli form) where defined, with the unit a two-sided identity.
A PCM *acts* on a value type `V` when the action respects unit and product.

"Compose when compatible" is exactly the PCM discipline, and the design note's
four combination rules are instances:

* `Reject E`: two non-unit effects never compose (the default);
* `Multiplicative M` / `Additive M`: total products on a commutative monoid;
* `Cap M` / `Floor M`: `min` / `max` on a semilattice with top / bottom;
* `Affine V M`: an optional absolute assignment plus a relative effect,
  composable iff at most one of the two is absolute.

The fold of a list of effects is the iterated partial product; we prove it is
invariant under permutation (so program order is irrelevant under PCMs) and,
for each shipped instance, that the fold is defined iff every *pair* of effects
is compatible (the "pairwise suffices" theorem that licenses the `O(n²)`
conflict check).
-/

namespace CategoricalInterventionsProofs

/-- A partial commutative monoid. `mul a b = none` means "`a` and `b` conflict". -/
class PCM (M : Type*) where
  one : M
  mul : M → M → Option M
  mul_comm : ∀ a b : M, mul a b = mul b a
  one_mul : ∀ a : M, mul one a = some a
  /-- Associativity in Kleisli form: `(a·b)·c = a·(b·c)`, both sides undefined
  or both defined and equal. -/
  mul_assoc : ∀ a b c : M,
    (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc)

/-- A bare action `act : M → V → V` of effects on values (no laws).  This is all
that is needed to *define* the semantics `P ▷ θ`; the laws in `PCMAction` are
what the composition theorems need. -/
class HasAct (M V : Type*) where
  act : M → V → V

/-- An action of a PCM on a value type, compatible with unit and product. -/
class PCMAction (M V : Type*) [PCM M] extends HasAct M V where
  act_one : ∀ v : V, act PCM.one v = v
  act_mul : ∀ (a b c : M) (v : V), PCM.mul a b = some c → act c v = act a (act b v)

/-- A PCM is *total* when every product is defined. -/
class PCMTotal (M : Type*) [PCM M] : Prop where
  mul_isSome : ∀ a b : M, (PCM.mul a b).isSome

export PCM (one mul mul_comm one_mul mul_assoc)
export HasAct (act)
export PCMAction (act_one act_mul)

section Basic
variable {M : Type*} [PCM M]

theorem mul_one (a : M) : mul a one = some a := by
  rw [mul_comm]; exact one_mul a

/-- The action of a defined product may be evaluated in either order. -/
theorem act_mul' {V : Type*} [PCMAction M V] {a b c : M} (v : V)
    (h : mul a b = some c) : act c v = act b (act a v) :=
  act_mul b a c v (by rw [mul_comm]; exact h)

end Basic

/-! ## Folding a list of effects -/

section Fold
variable {M : Type*} [PCM M]

/-- The iterated partial product of a list of effects, starting from `one`.
Defined by structural recursion (`foldList (m :: l) = m · foldList l`); see
`foldList_eq_foldl` for the equivalent left fold used by the Julia code. -/
def foldList : List M → Option M
  | [] => some one
  | m :: l => (foldList l).bind fun b => mul m b

@[simp] theorem foldList_nil : foldList ([] : List M) = some one := rfl

@[simp] theorem foldList_cons (m : M) (l : List M) :
    foldList (m :: l) = (foldList l).bind fun b => mul m b := rfl

@[simp] theorem foldList_singleton (m : M) : foldList [m] = some m := by
  simp [foldList, mul_one]

theorem bind_mul_one (o : Option M) : (o.bind fun b => mul one b) = o := by
  cases o <;> simp [one_mul]

/-- `foldList` agrees with the left fold `foldl (fun acc m => acc >>= (· * m)) (some one)`,
which is how the Julia implementation computes it. -/
theorem foldList_eq_foldl (l : List M) :
    foldList l = l.foldl (fun acc m => acc.bind fun a => mul a m) (some one) := by
  suffices h : ∀ (l : List M) (x : Option M),
      l.foldl (fun acc m => acc.bind fun a => mul a m) x =
        x.bind fun a => (foldList l).bind fun b => mul a b by
    rw [h]; exact (bind_mul_one _).symm
  intro l
  induction l with
  | nil => intro x; cases x <;> simp [mul_one]
  | cons m l ih =>
    intro x
    simp only [List.foldl_cons, foldList_cons]
    rw [ih]
    cases x with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      cases hl : foldList l with
      | none => simp
      | some b =>
        simp only [Option.bind_some]
        rw [mul_assoc]

/-- The fold of a concatenation is the product of the folds. -/
theorem foldList_append (l₁ l₂ : List M) :
    foldList (l₁ ++ l₂) = (foldList l₁).bind fun a => (foldList l₂).bind fun b => mul a b := by
  induction l₁ with
  | nil => simp [bind_mul_one]
  | cons m l ih =>
    simp only [List.cons_append, foldList_cons, ih]
    cases foldList l with
    | none => rfl
    | some a =>
      cases foldList l₂ with
      | none => simp
      | some b =>
        simp only [Option.bind_some]
        rw [mul_assoc]

/-- **Order irrelevance.** Permuting the list does not change the fold: under a
PCM, the order in which a program lists its atoms is irrelevant. -/
theorem fold_perm {l l' : List M} (h : l.Perm l') : foldList l = foldList l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l =>
    simp only [foldList_cons]
    cases foldList l with
    | none => rfl
    | some c =>
      simp only [Option.bind_some]
      have h1 := mul_assoc x y c
      have h2 := mul_assoc y x c
      rw [mul_comm x y] at h1
      rw [← h1, ← h2]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem foldList_isSome_of_cons {m : M} {l : List M}
    (h : (foldList (m :: l)).isSome) : (foldList l).isSome := by
  simp only [foldList_cons] at h
  rcases hl : foldList l with _ | c
  · simp [hl] at h
  · rfl

/-- For a total PCM the fold is always defined. -/
theorem foldList_isSome_of_total [PCMTotal M] (l : List M) : (foldList l).isSome := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [foldList_cons]
    rcases hl : foldList l with _ | b
    · simp [hl] at ih
    · simpa using PCMTotal.mul_isSome m b

end Fold

/-! ## The pairwise property

`PCMPairwise M` says the fold of a list is defined iff each element is
compatible with each later element, i.e. the fold is defined iff all pairs are.
It is stated via the two "cons" conditions, from which the pairwise
characterisation and downward closure under sublists follow generically. -/

/-- A PCM in which definedness of the fold is a pairwise condition. -/
class PCMPairwise (M : Type*) [PCM M] : Prop where
  /-- If `m · fold l` is defined, then `m` is compatible with every element of `l`. -/
  compat_of_fold_cons : ∀ (m : M) (l : List M),
    (foldList (m :: l)).isSome → ∀ b ∈ l, (mul m b).isSome
  /-- If `fold l` is defined and `m` is compatible with every element of `l`,
  then `m · fold l` is defined. -/
  fold_cons_of_compat : ∀ (m : M) (l : List M),
    (foldList l).isSome → (∀ b ∈ l, (mul m b).isSome) → (foldList (m :: l)).isSome

section Pairwise
variable {M : Type*} [PCM M] [PCMPairwise M]

/-- **Pairwise suffices.** The fold of a list is defined iff every pair of its
elements has a defined product. -/
theorem foldList_isSome_iff_pairwise (l : List M) :
    (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.pairwise_cons, ← ih]
    constructor
    · intro h
      exact ⟨PCMPairwise.compat_of_fold_cons m l h, foldList_isSome_of_cons h⟩
    · rintro ⟨h₁, h₂⟩
      exact PCMPairwise.fold_cons_of_compat m l h₂ h₁

/-- Definedness of the fold is inherited by sublists: dropping atoms never
creates a conflict. -/
theorem foldList_sublist {l₁ l₂ : List M} (h : l₁.Sublist l₂)
    (h₂ : (foldList l₂).isSome) : (foldList l₁).isSome := by
  rw [foldList_isSome_iff_pairwise] at *
  exact h₂.sublist h

end Pairwise

/-- Total PCMs are trivially pairwise. -/
instance (priority := low) PCMPairwise.ofTotal {M : Type*} [PCM M] [PCMTotal M] :
    PCMPairwise M where
  compat_of_fold_cons _ _ _ b _ := PCMTotal.mul_isSome _ b
  fold_cons_of_compat _ _ _ _ := foldList_isSome_of_total _

/-- **Pairwise suffices, total case.** For a total PCM the fold is always defined,
so both sides of the pairwise characterisation hold. -/
theorem fold_pairwise_total {M : Type*} [PCM M] [PCMTotal M] (l : List M) :
    (foldList l).isSome ∧ l.Pairwise (fun a b => (mul a b).isSome) :=
  ⟨foldList_isSome_of_total l, (foldList_isSome_iff_pairwise l).mp (foldList_isSome_of_total l)⟩

/-! ## Instance: `Reject` -/

/-- The default effect algebra: a unit adjoined to an arbitrary effect type `E`.
Two genuine effects never compose. -/
inductive Reject (E : Type*) where
  | unit : Reject E
  | eff : E → Reject E
  deriving DecidableEq

namespace Reject
variable {E : Type*}

/-- The partial product: defined iff one factor is the unit. -/
def mul : Reject E → Reject E → Option (Reject E)
  | unit, b => some b
  | a, unit => some a
  | eff _, eff _ => none

@[simp] theorem mul_unit_left (b : Reject E) : mul unit b = some b := by
  cases b <;> rfl

@[simp] theorem mul_unit_right (a : Reject E) : mul a unit = some a := by
  cases a <;> rfl

@[simp] theorem mul_eff_eff (a b : E) : mul (eff a) (eff b) = none := rfl

instance instPCM : PCM (Reject E) where
  one := unit
  mul := mul
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem pcm_one : (PCM.one : Reject E) = unit := rfl
@[simp] theorem pcm_mul (a b : Reject E) : PCM.mul a b = mul a b := rfl

/-- `fold l = unit` iff every element of `l` is the unit. -/
theorem foldList_eq_unit_iff (l : List (Reject E)) :
    foldList l = some unit ↔ ∀ b ∈ l, b = unit := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [foldList_cons, List.forall_mem_cons, ← ih]
    rcases hl : foldList l with _ | c
    · simp
    · simp only [Option.bind_some, pcm_mul]
      cases m <;> cases c <;> simp [mul]

/-- **Pairwise suffices for `Reject`.** A list of `Reject` effects folds to a
defined value iff it contains at most one genuine effect, i.e. iff all pairs are
compatible. -/
instance instPCMPairwise : PCMPairwise (Reject E) where
  compat_of_fold_cons m l h b hb := by
    simp only [foldList_cons] at h
    rcases hl : foldList l with _ | c
    · simp [hl] at h
    · rw [hl] at h
      simp only [Option.bind_some, pcm_mul] at h
      cases m with
      | unit => simp
      | eff e =>
        cases c with
        | eff _ => simp at h
        | unit =>
          have := (foldList_eq_unit_iff l).mp hl b hb
          subst this
          simp
  fold_cons_of_compat m l h hb := by
    simp only [foldList_cons]
    rcases hl : foldList l with _ | c
    · simp [hl] at h
    · simp only [Option.bind_some, pcm_mul]
      cases m with
      | unit => simp
      | eff e =>
        have hall : ∀ b ∈ l, b = unit := by
          intro b hb'
          have := hb b hb'
          cases b <;> simp_all
        have := (foldList_eq_unit_iff l).mpr hall
        rw [hl] at this
        cases this
        simp

/-- `Reject E` acts on `V` given an action of the raw effects `E`: the unit acts
trivially and `eff e` acts by `e`. -/
instance instAction {V : Type*} [HasAct E V] : PCMAction (Reject E) V where
  act
    | unit, v => v
    | eff e, v => act e v
  act_one v := rfl
  act_mul a b c v h := by
    cases a <;> cases b <;> simp [mul] at h <;> subst h <;> rfl

end Reject

theorem fold_pairwise_reject {E : Type*} (l : List (Reject E)) :
    (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome) :=
  foldList_isSome_iff_pairwise l

/-! ## Instances: `Multiplicative` and `Additive` -/

/-- Multiplicative effects: a commutative monoid `M` (e.g. `ℝ>0`) acting on itself
by multiplication.  Always composable. -/
structure Multiplicative (M : Type*) where
  val : M

namespace Multiplicative
variable {M : Type*} [CommMonoid M]

instance instPCM : PCM (Multiplicative M) where
  one := ⟨1⟩
  mul a b := some ⟨a.val * b.val⟩
  mul_comm a b := by simp [_root_.mul_comm]
  one_mul a := by simp
  mul_assoc a b c := by simp [_root_.mul_assoc]

instance instTotal : PCMTotal (Multiplicative M) := ⟨fun _ _ => rfl⟩

/-- Scaling a value: `act e v = e * v`. -/
instance instAction : PCMAction (Multiplicative M) M where
  act e v := e.val * v
  act_one v := by simp [PCM.one]
  act_mul a b c v h := by
    simp only [PCM.mul, Option.some.injEq] at h
    subst h
    simp [_root_.mul_assoc]

@[simp] theorem act_def (e : Multiplicative M) (v : M) : act e v = e.val * v := rfl

end Multiplicative

/-- Additive effects: an additive commutative monoid acting on itself by addition. -/
structure Additive (M : Type*) where
  val : M

namespace Additive
variable {M : Type*} [AddCommMonoid M]

instance instPCM : PCM (Additive M) where
  one := ⟨0⟩
  mul a b := some ⟨a.val + b.val⟩
  mul_comm a b := by simp [_root_.add_comm]
  one_mul a := by simp
  mul_assoc a b c := by simp [_root_.add_assoc]

instance instTotal : PCMTotal (Additive M) := ⟨fun _ _ => rfl⟩

/-- Shifting a value: `act e v = v + e`. -/
instance instAction : PCMAction (Additive M) M where
  act e v := v + e.val
  act_one v := by simp [PCM.one]
  act_mul a b c v h := by
    simp only [PCM.mul, Option.some.injEq] at h
    subst h
    show v + (a.val + b.val) = (v + b.val) + a.val
    rw [_root_.add_assoc, _root_.add_comm b.val a.val]

@[simp] theorem act_def (e : Additive M) (v : M) : act e v = v + e.val := rfl

end Additive

/-! ## Instances: `Cap` and `Floor` -/

/-- Capping effects: `min` on a meet-semilattice with a top (the unit). -/
structure Cap (M : Type*) where
  val : M

namespace Cap
variable {M : Type*} [SemilatticeInf M] [OrderTop M]

instance instPCM : PCM (Cap M) where
  one := ⟨⊤⟩
  mul a b := some ⟨a.val ⊓ b.val⟩
  mul_comm a b := by simp [inf_comm]
  one_mul a := by simp
  mul_assoc a b c := by simp [inf_assoc]

instance instTotal : PCMTotal (Cap M) := ⟨fun _ _ => rfl⟩

/-- Capping a value: `act e v = min e v`. -/
instance instAction : PCMAction (Cap M) M where
  act e v := e.val ⊓ v
  act_one v := by simp [PCM.one]
  act_mul a b c v h := by
    simp only [PCM.mul, Option.some.injEq] at h
    subst h
    simp [inf_assoc]

end Cap

/-- Flooring effects: `max` on a join-semilattice with a bottom (the unit). -/
structure Floor (M : Type*) where
  val : M

namespace Floor
variable {M : Type*} [SemilatticeSup M] [OrderBot M]

instance instPCM : PCM (Floor M) where
  one := ⟨⊥⟩
  mul a b := some ⟨a.val ⊔ b.val⟩
  mul_comm a b := by simp [sup_comm]
  one_mul a := by simp
  mul_assoc a b c := by simp [sup_assoc]

instance instTotal : PCMTotal (Floor M) := ⟨fun _ _ => rfl⟩

/-- Flooring a value: `act e v = max e v`. -/
instance instAction : PCMAction (Floor M) M where
  act e v := e.val ⊔ v
  act_one v := by simp [PCM.one]
  act_mul a b c v h := by
    simp only [PCM.mul, Option.some.injEq] at h
    subst h
    simp [sup_assoc]

end Floor

/-! ## Instance: `Affine` -/

/-- An affine effect: an optional absolute value plus a relative effect from `M`.
`(a, m)` means "set to `a` if present, then apply `m`". -/
@[ext]
structure Affine (V M : Type*) where
  abs : Option V
  rel : M

/-- Combine two optional absolutes: defined iff at most one is present. -/
def absMul {V : Type*} : Option V → Option V → Option (Option V)
  | some _, some _ => none
  | some x, none => some (some x)
  | none, y => some y

@[simp] theorem absMul_none_left {V : Type*} (y : Option V) : absMul none y = some y := by
  cases y <;> rfl
@[simp] theorem absMul_none_right {V : Type*} (x : Option V) : absMul x none = some x := by
  cases x <;> rfl
@[simp] theorem absMul_some_some {V : Type*} (x y : V) : absMul (some x) (some y) = none := rfl

namespace Affine
variable {V M : Type*} [PCM M]

/-- The product: defined iff at most one factor is absolute and the relative
parts compose; the result keeps whichever absolute is present. -/
def mul (a b : Affine V M) : Option (Affine V M) :=
  (absMul a.abs b.abs).bind fun x => (PCM.mul a.rel b.rel).map fun m => ⟨x, m⟩

theorem mul_mk (xa xb : Option V) (ma mb : M) :
    mul ⟨xa, ma⟩ ⟨xb, mb⟩ =
      (absMul xa xb).bind fun x => (PCM.mul ma mb).map fun m => (⟨x, m⟩ : Affine V M) := rfl

theorem bind_map_eq {α β γ : Type*} (o : Option α) (f : α → Option β) (g : β → γ) :
    (o.bind fun a => (f a).map g) = (o.bind f).map g := by
  cases o <;> rfl

theorem map_bind_eq {α β γ : Type*} (o : Option α) (f : α → β) (g : β → Option γ) :
    (o.map f).bind g = o.bind fun a => g (f a) := by
  cases o <;> rfl

theorem bind_const_none {α β : Type*} (o : Option α) :
    (o.bind fun _ => (none : Option β)) = none := by
  cases o <;> rfl

instance instPCM : PCM (Affine V M) where
  one := ⟨none, PCM.one⟩
  mul := mul
  mul_comm a b := by
    obtain ⟨xa, ma⟩ := a
    obtain ⟨xb, mb⟩ := b
    cases xa <;> cases xb <;> simp [mul_mk, PCM.mul_comm ma mb]
  one_mul a := by
    obtain ⟨xa, ma⟩ := a
    cases xa <;> simp [mul_mk, PCM.one_mul]
  mul_assoc a b c := by
    obtain ⟨xa, ma⟩ := a
    obtain ⟨xb, mb⟩ := b
    obtain ⟨xc, mc⟩ := c
    have key : ∀ (x : Option V),
        ((PCM.mul ma mb).bind fun m => (PCM.mul m mc).map fun m' => (⟨x, m'⟩ : Affine V M)) =
        ((PCM.mul mb mc).bind fun m => (PCM.mul ma m).map fun m' => (⟨x, m'⟩ : Affine V M)) := by
      intro x
      rw [bind_map_eq, bind_map_eq, PCM.mul_assoc]
    cases xa <;> cases xb <;> cases xc <;>
      simp only [mul_mk, absMul_none_left, absMul_none_right, absMul_some_some,
        Option.bind_some, Option.bind_none, map_bind_eq, bind_const_none, key]

@[simp] theorem pcm_one : (PCM.one : Affine V M) = ⟨none, PCM.one⟩ := rfl
@[simp] theorem pcm_mul (a b : Affine V M) : PCM.mul a b = mul a b := rfl

/-- The affine action: set to the absolute value if present, then apply the
relative effect. -/
instance instHasAct {W : Type*} [HasAct M W] : HasAct (Affine W M) W where
  act e v := act e.rel (e.abs.getD v)

omit [PCM M] in
@[simp] theorem act_def {W : Type*} [HasAct M W] (e : Affine W M) (v : W) :
    act e v = act e.rel (e.abs.getD v) := rfl

theorem act_one' {W : Type*} [PCMAction M W] (v : W) : act (PCM.one : Affine W M) v = v := by
  simp [act_one]

/-- The one-sided action law: `(a · b) ▷ v = a ▷ (b ▷ v)` whenever the product is
defined and `a` is purely relative (has no absolute part).  See `affine_action`
for why the two-sided law cannot hold. -/
theorem act_mul_of_abs_none {W : Type*} [PCMAction M W] {a b c : Affine W M} (v : W)
    (ha : a.abs = none) (h : PCM.mul a b = some c) : act c v = act a (act b v) := by
  obtain ⟨xa, ma⟩ := a
  obtain ⟨xb, mb⟩ := b
  obtain ⟨xc, mc⟩ := c
  simp only at ha
  subst ha
  simp only [pcm_mul, mul_mk, absMul_none_left, Option.bind_some, Option.map_eq_some_iff,
    Affine.mk.injEq] at h
  obtain ⟨m, hm, rfl, rfl⟩ := h
  cases xb <;> simp [act_mul ma mb m _ hm]

/-- When `y` is purely relative, applying `x` then `y` agrees with applying `x · y`. -/
theorem act_mul_of_relative {W : Type*} [PCMAction M W] {x y z : Affine W M} (v : W)
    (hy : y.abs = none) (h : PCM.mul x y = some z) : act z v = act y (act x v) :=
  act_mul_of_abs_none v hy (by rw [PCM.mul_comm]; exact h)

/-- The abstract law that does hold: a defined product acts by the product of the
relative parts on "the absolute if present, else the value". -/
theorem act_eq_of_mul {W : Type*} [HasAct M W] {x y z : Affine W M} (v : W)
    (h : PCM.mul x y = some z) : act z v = act z.rel ((x.abs.or y.abs).getD v) := by
  obtain ⟨xa, ma⟩ := x
  obtain ⟨xb, mb⟩ := y
  obtain ⟨xc, mc⟩ := z
  simp only [pcm_mul, mul_mk] at h
  cases xa <;> cases xb <;>
    simp only [absMul_none_left, absMul_none_right, absMul_some_some, Option.bind_some,
      Option.bind_none, Option.map_eq_some_iff, Affine.mk.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨m, hm, rfl, rfl⟩ := h
    rfl

theorem mul_isSome_iff [PCMTotal M] (a b : Affine V M) :
    (PCM.mul a b).isSome ↔ ¬ (a.abs.isSome ∧ b.abs.isSome) := by
  obtain ⟨xa, ma⟩ := a
  obtain ⟨xb, mb⟩ := b
  have := PCMTotal.mul_isSome ma mb
  cases xa <;> cases xb <;> simp [mul_mk, this]

/-- The absolute component of a defined fold is absent iff every element's is. -/
theorem fold_abs_none_iff {l : List (Affine V M)} {c : Affine V M}
    (h : foldList l = some c) : c.abs = none ↔ ∀ b ∈ l, b.abs = none := by
  induction l generalizing c with
  | nil => simp only [foldList_nil, Option.some.injEq] at h; subst h; simp
  | cons m l ih =>
    simp only [foldList_cons] at h
    rcases hl : foldList l with _ | d
    · simp [hl] at h
    · rw [hl] at h
      have ihd := ih hl
      obtain ⟨xm, mm⟩ := m
      obtain ⟨xd, md⟩ := d
      obtain ⟨xc, mc⟩ := c
      simp only [Option.bind_some, pcm_mul, mul_mk] at h
      simp only [List.mem_cons, forall_eq_or_imp]
      cases xm <;> cases xd <;>
        simp only [absMul_none_left, absMul_none_right, absMul_some_some, Option.bind_some,
          Option.bind_none, Option.map_eq_some_iff, Affine.mk.injEq, reduceCtorEq] at h ihd ⊢
      all_goals
        obtain ⟨_, _, rfl, _⟩ := h
        simp_all

/-- **Pairwise suffices for `Affine`.** Over a total relative algebra, a list of
affine effects folds to a defined value iff at most one is absolute, i.e. iff all
pairs are compatible. -/
instance instPCMPairwise [PCMTotal M] : PCMPairwise (Affine V M) where
  compat_of_fold_cons m l h b hb := by
    simp only [foldList_cons] at h
    rcases hl : foldList l with _ | c
    · simp [hl] at h
    · rw [hl] at h
      simp only [Option.bind_some] at h
      rw [mul_isSome_iff] at h ⊢
      intro ⟨hm, hb'⟩
      apply h
      refine ⟨hm, ?_⟩
      by_contra hc
      have hc' : c.abs = none := by
        cases hx : c.abs with
        | none => rfl
        | some _ => exact absurd (by simp [hx]) hc
      have := (fold_abs_none_iff hl).mp hc' b hb
      simp [this] at hb'
  fold_cons_of_compat m l h hb := by
    simp only [foldList_cons]
    rcases hl : foldList l with _ | c
    · simp [hl] at h
    · simp only [Option.bind_some]
      rw [mul_isSome_iff]
      intro ⟨hm, hc⟩
      have hall : ∀ b ∈ l, b.abs = none := by
        intro b hb'
        have := hb b hb'
        rw [mul_isSome_iff] at this
        cases hx : b.abs with
        | none => rfl
        | some _ => exact absurd ⟨hm, by simp [hx]⟩ this
      have := (fold_abs_none_iff hl).mpr hall
      simp [this] at hc

end Affine

/-- **`Affine` is a PCM**: the product `(a, m) · (a', m') = (a ∨ a', m · m')`,
defined iff at most one absolute is present, is commutative, associative, and
has unit `(none, 1)`. -/
theorem affine_pcm {V M : Type*} [PCM M] (a b c : Affine V M) :
    mul a b = mul b a ∧ mul one a = some a ∧
    (mul a b).bind (fun ab => mul ab c) = (mul b c).bind (fun bc => mul a bc) :=
  ⟨mul_comm a b, one_mul a, mul_assoc a b c⟩

/-- **`Affine` acts**: `(a, m) ▷ v = m ▷ (a if present else v)` respects the unit,
and respects defined products *one-sidedly*: `(a · b) ▷ v = a ▷ (b ▷ v)` whenever
`a` is purely relative.

The two-sided law of `PCMAction` (`act_mul` for *all* compatible pairs) cannot
hold for `Affine`: with `a = (some x, 1)` and `b = (none, m)` we have
`(a · b) ▷ v = m ▷ x` but `a ▷ (b ▷ v) = x`.  "Set, then scale" is the intended
semantics; it means absolute assignments must be applied before relative ones,
which is exactly what folding first and acting once (`apply`) does.  So `Affine`
carries a `HasAct` instance (enough to define `apply`) but not a `PCMAction`
instance, and the homomorphism theorem `apply_append` applies to `Affine`
programs only when the later program is purely relative. -/
theorem affine_action {V M : Type*} [PCM M] [PCMAction M V] (x y z : Affine V M) (v : V) :
    act (one : Affine V M) v = v ∧
    (mul x y = some z → act z v = act z.rel ((x.abs.or y.abs).getD v)) ∧
    act x v = act x.rel (x.abs.getD v) :=
  ⟨Affine.act_one' v, fun h => Affine.act_eq_of_mul v h, rfl⟩

/-- When the later program element `y` is purely relative, sequential application
`x` then `y` agrees with the product: `(x · y) ▷ v = y ▷ (x ▷ v)`. -/
theorem affine_act_mul_of_relative {V M : Type*} [PCM M] [PCMAction M V] {x y z : Affine V M}
    (v : V) (hy : y.abs = none) (h : mul x y = some z) : act z v = act y (act x v) :=
  Affine.act_mul_of_relative v hy h

/-- Symmetric form: when `x` is purely relative, `(x · y) ▷ v = x ▷ (y ▷ v)`. -/
theorem affine_act_mul_of_relative' {V M : Type*} [PCM M] [PCMAction M V] {x y z : Affine V M}
    (v : V) (hx : x.abs = none) (h : mul x y = some z) : act z v = act x (act y v) :=
  Affine.act_mul_of_abs_none v hx h

theorem fold_pairwise_affine {V M : Type*} [PCM M] [PCMTotal M] (l : List (Affine V M)) :
    (foldList l).isSome ↔ l.Pairwise (fun a b => (mul a b).isSome) :=
  foldList_isSome_iff_pairwise l

/-- For `Affine` over a total algebra, "all pairs compatible" is "at most one
absolute": the fold is defined iff no two elements both carry an absolute. -/
theorem fold_affine_isSome_iff {V M : Type*} [PCM M] [PCMTotal M] (l : List (Affine V M)) :
    (foldList l).isSome ↔ l.Pairwise (fun a b => ¬ (a.abs.isSome ∧ b.abs.isSome)) := by
  rw [fold_pairwise_affine]
  constructor <;> intro h <;> refine h.imp ?_ <;> intro a b
  · exact (Affine.mul_isSome_iff a b).mp
  · exact (Affine.mul_isSome_iff a b).mpr

end CategoricalInterventionsProofs
