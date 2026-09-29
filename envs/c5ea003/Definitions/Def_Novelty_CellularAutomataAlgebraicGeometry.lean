-- Prove2me | Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry
-- name    : Novelty_CellularAutomataAlgebraicGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:29.463273+00:00
-- url     : https://prove2.me/theorems/5022caed-1dbe-48d7-8b72-76e68c731c04
-- title:
--   Aether Catalog definitions — Novelty_CellularAutomataAlgebraicGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CellularAutomataAlgebraicGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CellularAutomataAlgebraicGeometry.lean by skeleton subtraction
import Mathlib

/-!
# Elementary cellular automata as polynomial maps

This file formalizes elementary cellular automata on bi-infinite Boolean
configurations.  It identifies the algebraic normal form of Rule 110 and proves
that Rule 0 has one fixed configuration, whereas Rule 204 fixes every
configuration.  An explicit configuration shows that Rule 110 does not have
all states as fixed points.
-/

namespace CellularAutomataAlgebraicGeometry

/-- The Wolfram truth-table index of a three-cell Boolean neighborhood. -/
def neighborhoodIndex (left center right : Bool) : Nat :=
  4 * left.toNat + 2 * center.toNat + right.toNat

/-- The local Boolean function encoded by a Wolfram elementary rule number. -/
def localRule (rule : Nat) (left center right : Bool) : Bool :=
  (rule.testBit (neighborhoodIndex left center right))

/-- The synchronous global update on a bi-infinite Boolean configuration. -/
def globalUpdate (rule : Nat) (state : Int → Bool) : Int → Bool :=
  fun i => localRule rule (state (i - 1)) (state i) (state (i + 1))








end CellularAutomataAlgebraicGeometry


