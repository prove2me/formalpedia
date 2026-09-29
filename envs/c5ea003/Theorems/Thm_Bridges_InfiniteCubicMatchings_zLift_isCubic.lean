-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_zLift_isCubic
-- name    : Bridges.InfiniteCubicMatchings.zLift_isCubic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:31.465145+00:00
-- url     : https://prove2.me/theorems/4bdbf2a0-9597-4df7-b235-ac30a6fc8d96
-- title:
--   ZLift isCubic
-- statement:
--   Formal statement of `Bridges.InfiniteCubicMatchings.zLift_isCubic` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.zLift_isCubic(hK : IsCubic K) : IsCubic (zLift K vol hvol) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsPetersenLift.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsPetersenLift.lean#L67

-- Thm stub generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
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

theorem Bridges.InfiniteCubicMatchings.zLift_isCubic(hK : IsCubic K) : IsCubic (zLift K vol hvol) := by sorry
