-- Prove2me | Definitions.Def_Logic_DreamLogic_BelnapAlgebra
-- name    : Logic_DreamLogic_BelnapAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:13.749888+00:00
-- url     : https://prove2.me/theorems/33c71baa-bd5c-4f78-b06e-21fde4d02737
-- title:
--   Aether Catalog definitions — Logic_DreamLogic_BelnapAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DreamLogic.BelnapAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DreamLogic/BelnapAlgebra.lean by skeleton subtraction
import Mathlib
/-
# Belnap's FOUR as a Bounded Distributive Lattice: Gluts, Gaps, and Paraconsistency

This file gives a fully self-contained development of Belnap's four-valued logic `FOUR`
(`N` = neither/gap, `F` = false, `T` = true, `B` = both/glut) as a **bounded distributive
lattice** under the *truth ordering*, and proves the central metalogical fact that
*paraconsistency is equivalent to the existence of a designated glut*.

The truth order is the De Morgan / FDE order `F ≤ N, B ≤ T` (a four-element diamond,
isomorphic to `Bool × Bool` via the "evidence-for / evidence-against" coordinates).
Negation `neg` is the order-reversing De Morgan involution.

## Main results
* `Belnap` is given genuine `DistribLattice` and `BoundedOrder` instances (`⊥ = F`, `⊤ = T`).
* `neg_neg`, `neg_antitone`, `neg_inf`, `neg_sup` — `neg` is a De Morgan involution.
* `glut_iff_B`, `gap_iff_N` — the unique glut is `B`, the unique gap is `N`.
* `paraconsistency_iff_glut` — FOUR is non-explosive **iff** it has a designated glut.
* `card_four` — FOUR has exactly four elements.

-- !-- Lab Notebook -- !--
Hypothesis: Belnap's FOUR, ordered by truth, is a bounded distributive lattice, and its
  paraconsistency is *exactly* the existence of a glut (a designated value with designated
  negation). The lattice should be the diamond `2 × 2`.
Result: All instances and characterization theorems below are discharged by `decide`
  (finite four-element carrier) once the order is encoded through the `Bool × Bool`
  coordinates. `paraconsistency_iff_glut` makes the glut the *cause* of non-explosion.
Insight: Encoding `tle` through the twisted product order on `Bool × Bool` makes meet/join
  literally componentwise Boolean operations, so distributivity, the bounds, and the De
  Morgan laws all become finite Boolean identities — `decide` closes everything uniformly.
Failure analysis: Building `OrderBot`/`OrderTop` via anonymous-constructor `⟨F, _⟩` fails
  because `Bot`/`Top` are separate classes; supplying the `bot`/`top` fields explicitly in
  the `where` block fixes it. Defining `tle` directly as a `Prop` conjunction (rather than
  a `Bool`) loses the cheap `DecidableRel`, so we route through `tleb : Bool`.
-/


namespace DreamLogic

/-- Belnap's four truth values: `N` (neither / truth-value gap), `F` (false), `T` (true),
`B` (both / truth-value glut). -/
inductive Belnap | N | F | T | B
deriving DecidableEq, Fintype, Repr

namespace Belnap

/-- De Morgan negation on FOUR: it fixes the gap `N` and the glut `B` and swaps `F`/`T`. -/
def neg : Belnap → Belnap
  | N => N | F => T | T => F | B => B

/-- The "evidence-for / evidence-against" coordinates of a Belnap value in `Bool × Bool`
(Ginsberg's `2 ⊙ 2` representation). -/
def toProd : Belnap → Bool × Bool
  | N => (false, false) | F => (false, true) | T => (true, false) | B => (true, true)

/-- The truth order as a decidable Boolean predicate: more evidence-for and less
evidence-against. -/
def tleb (a b : Belnap) : Bool :=
  (decide ((toProd a).1 ≤ (toProd b).1)) && (decide ((toProd b).2 ≤ (toProd a).2))

instance : LE Belnap := ⟨fun a b => tleb a b = true⟩

instance : DecidableRel ((· ≤ ·) : Belnap → Belnap → Prop) :=
  fun a b => inferInstanceAs (Decidable (tleb a b = true))

/-- Truth meet ("and"): componentwise `&&` on evidence-for, `||` on evidence-against. -/
def tmeet (a b : Belnap) : Belnap :=
  match (toProd a).1 && (toProd b).1, (toProd a).2 || (toProd b).2 with
  | false, false => N | false, true => F | true, false => T | true, true => B

/-- Truth join ("or"): componentwise `||` on evidence-for, `&&` on evidence-against. -/
def tjoin (a b : Belnap) : Belnap :=
  match (toProd a).1 || (toProd b).1, (toProd a).2 && (toProd b).2 with
  | false, false => N | false, true => F | true, false => T | true, true => B

/-! ## The bounded distributive lattice structure -/

-- !-- Each lattice law is a finite identity over the four-element carrier, closed by
-- `decide` after encoding the order/operations via `Bool × Bool`. -- !--
instance : Lattice Belnap where
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := tjoin
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := tmeet
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

/-- **FOUR is distributive.** Under the truth order, the four-element diamond `2 × 2`
satisfies the distributive law. -/
instance : DistribLattice Belnap where
  le_sup_inf := by decide

instance : OrderBot Belnap where
  bot := F
  bot_le := by decide

instance : OrderTop Belnap where
  top := T
  le_top := by decide

/-- **FOUR is a bounded distributive lattice** with bottom `F` and top `T`. -/
instance : BoundedOrder Belnap where


/-! ## Negation is a De Morgan involution -/

-- !-- Finite check: `neg` composed with itself is the identity on the four values. -- !--

-- !-- Finite check: negation reverses the truth order (order-reversing De Morgan map). -- !--

-- !-- The two De Morgan laws are finite Boolean identities on the carrier. -- !--


/-! ## Designation, gluts, and gaps -/

/-- The designated ("at least true") values are `T` and `B`: a sentence is assertible
exactly when its value is designated. -/
def designated (a : Belnap) : Prop := a = T ∨ a = B

instance : DecidablePred designated := fun a => by unfold designated; infer_instance

/-- A **glut** is a designated value whose negation is also designated (a value that is
"both true and false"). -/
def IsGlut (a : Belnap) : Prop := designated a ∧ designated (neg a)

/-- A **gap** is a non-designated value whose negation is also non-designated (a value
that is "neither true nor false"). -/
def IsGap (a : Belnap) : Prop := ¬ designated a ∧ ¬ designated (neg a)

instance : DecidablePred IsGlut := fun a => by unfold IsGlut; infer_instance
instance : DecidablePred IsGap := fun a => by unfold IsGap; infer_instance

-- !-- Finite check: the only value designated together with its negation is `B`. -- !--

-- !-- Finite check: the only value non-designated together with its negation is `N`. -- !--

/-! ## Paraconsistency -/

/-- The **explosion principle** (`ex contradictione quodlibet`): a designated value with a
designated negation entails every conclusion. A logic is *explosive* if this holds. -/
def Explosive : Prop :=
  ∀ a q : Belnap, designated a → designated (neg a) → designated q

-- !-- Non-explosion ⇔ a glut exists: with witness conclusion `q = F` non-designated, the
-- explosion rule fails exactly when some value is designated with designated negation. -- !--


/-! ## Minimality -/


end Belnap
end DreamLogic


