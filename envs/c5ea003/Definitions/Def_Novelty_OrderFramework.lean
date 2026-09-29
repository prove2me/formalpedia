-- Prove2me | Definitions.Def_Novelty_OrderFramework
-- name    : Novelty_OrderFramework
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:38.123805+00:00
-- url     : https://prove2.me/theorems/c65ec5c4-48e8-4340-bde6-a6f074093b53
-- title:
--   Aether Catalog definitions — Novelty_OrderFramework
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OrderFramework`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OrderFramework.lean by skeleton subtraction
import Mathlib
/-
  Minor-Closed Graph Classes — Order-Theoretic Framework
  ======================================================

  This file develops the abstract order-theoretic backbone of the theory of
  *minor-closed graph classes*.  We work in a generic ordered type `α` in which
  the relation `x ≤ y` is read as "`x` is a minor of `y`".  Every concrete model
  of the graph-minor relation (or any sub-relation of it, such as the subgraph
  order — see `ForestDensity.lean`) is an instance of this framework.

  A *graph class* is a set `C : Set α`; it is **minor-closed** when it is downward
  closed under the minor relation.  The fundamental construction is `excl S`, the
  class of objects that exclude every member of `S` as a minor.  The key results
  formalise the *easy half of the Robertson–Seymour philosophy*:

  * `excl_minorClosed`              : every excluded-minor class is minor-closed.
  * `minorClosed_excl_obstructions` : conversely, over a well-founded minor order
                                      every minor-closed class is the class of
                                      graphs excluding its set of minimal
                                      obstructions.
  * `obstructions_excl_singleton`   : the obstruction set of a single-excluded-minor
                                      class `excl {H}` is exactly `{H}`.
  * `singleExcludedMinor_iff_obstructions_singleton`
                                    : a minor-closed class is characterised by a
                                      single forbidden minor **iff** its obstruction
                                      set is a singleton.

  The last statement is the abstract form of the mission's target: *being
  characterised by a single forbidden minor* is equivalent to *having a single
  minimal obstruction*.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): "Minor-closed = exclude a set of forbidden minors"
    should be a theorem, not a definition, given well-foundedness of the order.
  Experiment (Experimenter): formalised `excl`, `obstructions`, and proved the
    round trip `MinorClosed C ↔ C = excl (obstructions C)` under `WellFoundedLT`.
  Analysis (Analyst): the forward direction needs only downward closure +
    transitivity; the reverse direction is exactly where well-foundedness enters
    (to extract a *minimal* forbidden minor below any excluded graph).
  Critique (Critic): uniqueness of the obstruction of `excl {H}` genuinely needs
    antisymmetry (`PartialOrder`), not merely a preorder — a preorder allows
    `H ≤ m ≤ H` with `m ≠ H`.  Statement guarded accordingly.
  Synthesis (PI): the single-forbidden-minor property reduces to a singleton
    obstruction set; this is the order-theoretic core of the 3/2 conjecture.
  -- !-- Lab Notes -- !--
-/

namespace MinorTheory

variable {α : Type*}

section Preorder
variable [Preorder α]

/-- A graph class `C` is **minor-closed** when it is downward closed under the
minor relation `· ≤ ·`. -/
def MinorClosed (C : Set α) : Prop := ∀ ⦃x y : α⦄, x ≤ y → y ∈ C → x ∈ C

/-- `excl S` is the class of objects excluding every member of `S` as a minor. -/
def excl (S : Set α) : Set α := {x | ∀ ⦃s⦄, s ∈ S → ¬ s ≤ x}








/-- The set of **minimal obstructions** of a class `C`: graphs outside `C` all of
whose proper minors lie in `C`. -/
def obstructions (C : Set α) : Set α := {m | m ∉ C ∧ ∀ x, x < m → x ∈ C}

/-- A class is characterised by a **single forbidden minor** if it equals
`excl {H}` for some `H`. -/
def SingleExcludedMinor (C : Set α) : Prop := ∃ H : α, C = excl {H}


end Preorder

section WellFounded
variable [Preorder α] [WellFoundedLT α]



end WellFounded

section PartialOrder
variable [PartialOrder α]


end PartialOrder

section Characterisation
variable [PartialOrder α] [WellFoundedLT α]


end Characterisation

end MinorTheory


