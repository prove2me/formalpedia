-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_zLift_edgeSet_infinite
-- name    : Bridges.InfiniteCubicMatchings.zLift_edgeSet_infinite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:23.74791+00:00
-- url     : https://prove2.me/theorems/16d73cfb-e46a-4479-8902-fc96d36a624e
-- title:
--   A ℤ-voltage lift of a graph with at least one edge has infinitely many edges: the
-- statement:
--   A ℤ-voltage lift of a graph with at least one edge has infinitely many edges: the
--   whole ℤ-orbit of any base edge survives in the lift.  In particular the lift is a genuinely
--   infinite graph, not a finite one in disguise.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.zLift_edgeSet_infinite{u v : W} (huv : K.Adj u v) :
--       ((zLift K vol hvol).edgeSet).Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsPetersenLift.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsPetersenLift.lean#L82

-- Thm stub generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
/-
# Infinite ℤ-voltage lifts, and an infinite Berge–Fulkerson graph over the Petersen graph

The examples of §`InfiniteCubicMatchingsLadder` are all 3-edge-colourable, which makes the
Berge–Fulkerson property cheap.  Here we produce infinite witnesses over an arbitrary base:

* `zLift K vol` is the ℤ-voltage lift of a graph `K` along an antisymmetric voltage function.
  It is always an infinite graph covering `K` (`isLocalIsoAt_zLift`), it is cubic whenever `K`
  is (`zLift_isCubic`), and it inherits the Berge–Fulkerson and Fan–Raspaud properties
  (`zLift_bergeFulkerson`, `zLift_fanRaspaud`).
* `petersen` is the Petersen graph, the standard example of a cubic bridgeless graph that is
  **not** 3-edge-colourable.  Its six perfect matchings are written out explicitly and the
  Berge–Fulkerson condition is verified by kernel computation (`petersen_bergeFulkerson`).
* Consequently `zLift petersen vol` is an infinite cubic graph satisfying all three
  properties, obtained from a base that admits no proper 3-edge-colouring.
-/

open Bridges.InfiniteCubicMatchings

universe v

/-! ## ℤ-voltage lifts -/


variable {W : Type v} (K : SimpleGraph W) (vol : W → W → ℤ)


variable (hvol : ∀ u v : W, vol v u = -vol u v)

theorem Bridges.InfiniteCubicMatchings.zLift_edgeSet_infinite{u v : W} (huv : K.Adj u v) :
    ((zLift K vol hvol).edgeSet).Infinite := by sorry
