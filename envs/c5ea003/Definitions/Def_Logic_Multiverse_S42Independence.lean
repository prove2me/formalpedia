-- Prove2me | Definitions.Def_Logic_Multiverse_S42Independence
-- name    : Logic_Multiverse_S42Independence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:58:58.765961+00:00
-- url     : https://prove2.me/theorems/2237ad60-95e0-40d1-9ea2-0c1d596ad5bb
-- title:
--   Aether Catalog definitions — Logic_Multiverse_S42Independence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.S42Independence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/S42Independence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_InvariantFragment
/-
# `S4.2` Soundness for Directed Preorders, and Independence of `5` and `.3`

This file completes the calibration begun in
`Catalog/Logic/Multiverse/InvariantFragment.lean` by supplying the *deductive*
half of Direction 2 of the multiverse programme.

We define a modal language, its Kripke semantics, and a Hilbert calculus for
**`S4.2`** (classical propositional logic together with `K`, `T`, `4` and the
directedness axiom `.2`, closed under modus ponens and necessitation), and prove:

* `S42_sound` — **every theorem of `S4.2` is valid on every directed preorder**
  (induction on derivations; the `.2` case is exactly where directedness is used);
* `five_not_derivable` — the axiom `5` (`◇p → □◇p`) is **not** derivable in `S4.2`,
  because it fails on the finite button–switch forcing frame of the realization
  file, which *is* a directed preorder;
* `dot3_not_derivable` — the linearity axiom `.3`
  (`□(□p → q) ∨ □(□q → p)`) is **not** derivable in `S4.2` either: two independent
  buttons refute it.

Together with `BooleanValuedRealization.cacc_dot2` (soundness of `.2` on the frame)
and `MultiverseInvariantFragment.directed_of_dot2` (its exact semantic content),
this shows the modal logic of the finite pre-Boolean forcing frames contains `S4.2`
and is strictly below both `S5` and `S4.3`.
-/

namespace S42Independence

open BooleanValuedRealization MultiverseInvariantFragment

/-! ## The modal language and its Kripke semantics -/

/-- Modal formulas over propositional atoms `α`. -/
inductive MForm (α : Type*) where
  | atom : α → MForm α
  | fls : MForm α
  | imp : MForm α → MForm α → MForm α
  | box : MForm α → MForm α
  deriving DecidableEq

namespace MForm
variable {α : Type*}

/-- Negation. -/
def neg (p : MForm α) : MForm α := .imp p .fls
/-- Disjunction. -/
def disj (p q : MForm α) : MForm α := .imp (neg p) q
/-- Possibility. -/
def dia (p : MForm α) : MForm α := neg (.box (neg p))

end MForm

variable {α W : Type*}

/-- Kripke satisfaction. -/
def msat (R : W → W → Prop) (V : α → W → Prop) : MForm α → W → Prop
  | .atom a => V a
  | .fls => fun _ => False
  | .imp p q => fun w => msat R V p w → msat R V q w
  | .box p => fun w => ∀ v, R w v → msat R V p v




/-! ## The Hilbert calculus `S4.2` -/

/-- Derivability in `S4.2`: classical propositional logic (`ax1`–`ax3`) with the
modal axioms `K`, `T`, `4`, `.2`, closed under modus ponens and necessitation. -/
inductive S42 {α : Type*} : MForm α → Prop
  | ax1 (p q : MForm α) : S42 (.imp p (.imp q p))
  | ax2 (p q r : MForm α) :
      S42 (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | ax3 (p : MForm α) : S42 (.imp (MForm.neg (MForm.neg p)) p)
  | axK (p q : MForm α) :
      S42 (.imp (.box (.imp p q)) (.imp (.box p) (.box q)))
  | axT (p : MForm α) : S42 (.imp (.box p) p)
  | ax4 (p : MForm α) : S42 (.imp (.box p) (.box (.box p)))
  | axDot2 (p : MForm α) : S42 (.imp (MForm.dia (.box p)) (.box (MForm.dia p)))
  | mp {p q : MForm α} : S42 (.imp p q) → S42 p → S42 q
  | nec {p : MForm α} : S42 p → S42 (.box p)

/-- A **directed preorder**: the abstract shape of a forcing frame. -/
structure DirectedPreorder (W : Type*) where
  /-- The accessibility relation. -/
  rel : W → W → Prop
  refl : ∀ w, rel w w
  trans : ∀ {w v u}, rel w v → rel v u → rel w u
  dir : ∀ x y z, rel x y → rel x z → ∃ u, rel y u ∧ rel z u


/-! ## The finite control frame as a directed preorder -/

/-- The two-button, one-switch forcing frame, packaged as a directed preorder. -/
def ctrlFrame : DirectedPreorder (CWorld Bool Unit) where
  rel := cacc
  refl := fun _ => subset_rfl
  trans := fun h1 h2 => h1.trans h2
  dir := fun _ y z _ _ =>
    ⟨(y.1 ∪ z.1, y.2), Finset.subset_union_left, Finset.subset_union_right⟩

/-- The base world: no button pushed. -/
def w₀ : CWorld Bool Unit := (∅, fun _ => false)

/-- Valuation used for the countermodels: atom `a` says "button `a` is pushed",
except that we also use the negated form for the failure of `5`. -/
def Vpush : Bool → CWorld Bool Unit → Prop := fun b w => b ∈ w.1

/-- Valuation saying "button `a` is *not* pushed". -/
def Vunpushed : Bool → CWorld Bool Unit → Prop := fun b w => b ∉ w.1

/-! ## Independence of `5` -/



/-! ## Independence of `.3` -/

/-- The linearity axiom `.3` for two atoms. -/
def dot3Formula : MForm Bool :=
  MForm.disj (.box (.imp (.box (.atom true)) (.atom false)))
    (.box (.imp (.box (.atom false)) (.atom true)))




end S42Independence


