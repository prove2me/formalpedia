-- Prove2me | Definitions.Def_Logic_DreamLogic_BelnapKnowledgeOrder
-- name    : Logic_DreamLogic_BelnapKnowledgeOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:11.719866+00:00
-- url     : https://prove2.me/theorems/c1f09ca3-6133-4e7a-9bef-898018f6c70a
-- title:
--   Aether Catalog definitions — Logic_DreamLogic_BelnapKnowledgeOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DreamLogic.BelnapKnowledgeOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DreamLogic/BelnapKnowledgeOrder.lean by skeleton subtraction
import Mathlib

/-!
# Belnap's FOUR — the Knowledge (Information) Order

This file formalizes Belnap's four-valued logic `FOUR` from the point of view of
the **knowledge order** (a.k.a. the *information order*).  The four values record
*how much evidence* we have about a proposition, split into a "truth bit" and a
"falsity bit":

* `neither`   — no evidence either way      `(false, false)`
* `onlyTrue`  — evidence only for truth      `(true,  false)`
* `onlyFalse` — evidence only for falsity    `(false, true)`
* `both`      — evidence for both            `(true,  true)`

The knowledge order is the *componentwise* (product) order on these two bits:
more information is higher.  Its join `kjoin` accumulates evidence (componentwise
`or`) and its meet `kmeet` keeps only common evidence (componentwise `and`).
With these operations `FOUR` is a bounded lattice (a copy of the Boolean square),
with bottom `neither` and top `both`.

We then study the predicate `defaultTrue x := (equivBits x).2 = false`, "there is
no evidence of falsity".  This is the closed-world / negation-as-failure default.
It is **not monotone** with respect to the knowledge order: gaining evidence of
falsity destroys it.  Consequently `{x | defaultTrue x}` is **not an upper set**,
and hence **not open** in the Alexandrov (upper-set) topology of the knowledge
order.

## Main results

* `DreamLogic.FOUR_is_bounded_lattice` — `(FOUR, kle, kjoin, kmeet)` is a bounded
  lattice with `⊥ = neither` and `⊤ = both`.
* `DreamLogic.defaultTrue_non_monotone` — `neither ≤ onlyFalse` in the knowledge
  order, yet `defaultTrue neither` holds while `defaultTrue onlyFalse` fails.
* `DreamLogic.defaultTrue_not_upperSet` — `{x | defaultTrue x}` is not an upper
  set for `kle`.
* `DreamLogic.defaultTrue_not_open` — `{x | defaultTrue x}` is not open in the
  upper-set (Alexandrov) topology induced by `kle`.
-/

namespace DreamLogic

/-- Belnap's four truth values, viewed through the knowledge / information order. -/
inductive FOUR
  | neither
  | onlyTrue
  | onlyFalse
  | both
  deriving DecidableEq, Repr, Fintype

namespace FOUR

/-- The canonical encoding of `FOUR` as a pair of bits `(truth-bit, falsity-bit)`. -/
def equivBits : FOUR ≃ Bool × Bool where
  toFun
    | neither => (false, false)
    | onlyTrue => (true, false)
    | onlyFalse => (false, true)
    | both => (true, true)
  invFun
    | (false, false) => neither
    | (true, false) => onlyTrue
    | (false, true) => onlyFalse
    | (true, true) => both
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- The knowledge order: the product order on `Bool × Bool`, transported via
`equivBits`.  "More information" is higher. -/
def kle (x y : FOUR) : Prop := equivBits x ≤ equivBits y

instance : DecidableRel kle := fun x y => by unfold kle; infer_instance

/-- Knowledge join: accumulate evidence (componentwise `or`). -/
def kjoin (x y : FOUR) : FOUR := equivBits.symm (equivBits x ⊔ equivBits y)

/-- Knowledge meet: keep only common evidence (componentwise `and`). -/
def kmeet (x y : FOUR) : FOUR := equivBits.symm (equivBits x ⊓ equivBits y)

/-- The "no evidence of falsity" default: the falsity bit is `false`. -/
def defaultTrue (x : FOUR) : Prop := (equivBits x).2 = false

instance : DecidablePred defaultTrue := fun x => by unfold defaultTrue; infer_instance

/-! ### The bounded-lattice instance on `FOUR` -/

instance instLattice : Lattice FOUR where
  le := kle
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := kjoin
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := kmeet
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance instDecidableLE : DecidableRel (α := FOUR) (· ≤ ·) :=
  fun x y => (inferInstance : Decidable (kle x y))

instance instBoundedOrder : BoundedOrder FOUR where
  top := both
  bot := neither
  le_top := by decide
  bot_le := by decide


/-! ### Non-monotonicity of the closed-world default -/




end FOUR
end DreamLogic


