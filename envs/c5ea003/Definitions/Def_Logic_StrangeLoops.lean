-- Prove2me | Definitions.Def_Logic_StrangeLoops
-- name    : Logic_StrangeLoops
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:51.682183+00:00
-- url     : https://prove2.me/theorems/40b19db5-1bc9-4d36-80ab-ed3fa5e94c40
-- title:
--   Aether Catalog definitions — Logic_StrangeLoops
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.StrangeLoops`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/StrangeLoops.lean by skeleton subtraction
import Mathlib
import Mathlib.Order.Basic

/-!
# Strange loops and abstract incompleteness

This file isolates the order-theoretic core of a Gödel sentence.  A formal
system is represented externally by a predicate `Prov : Sentence → Prop`.
A strange loop is a sentence `g` satisfying `g ↔ ¬ Prov g`.

The results deliberately separate the diagonal/fixed-point hypothesis from
soundness.  They also give finite countermodels to two tempting but false
unqualified conjectures.
-/

namespace StrangeLoops

/-- A sentence that asserts its own unprovability (at the metalevel). -/
def IsGodelFixedPoint {Sentence : Type*} (Prov : Sentence → Prop)
    (meaning : Sentence → Prop) (g : Sentence) : Prop :=
  meaning g ↔ ¬ Prov g

/-- Semantic reflection/soundness for the represented provability predicate. -/
def Reflects {Sentence : Type*} (Prov : Sentence → Prop)
    (meaning : Sentence → Prop) : Prop :=
  ∀ s, Prov s → meaning s



section PropositionalLattice

/-- Monotonicity is the order-theoretic condition on a provability operator on
`Prop`, ordered by implication. -/
def MonotoneProv (P : Prop → Prop) : Prop :=
  ∀ ⦃a b : Prop⦄, (a → b) → P a → P b



/-- A provability predicate decides every proposition when it proves either it
or its negation. -/
def SyntacticallyComplete (P : Prop → Prop) : Prop :=
  ∀ a : Prop, P a ∨ P (¬ a)

/-- A minimal consistency condition. -/
def Consistent (P : Prop → Prop) : Prop := ¬ P False




end PropositionalLattice

end StrangeLoops


