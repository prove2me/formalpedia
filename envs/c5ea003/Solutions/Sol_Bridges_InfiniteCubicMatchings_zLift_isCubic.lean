-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.zLift_isCubic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:50:01.454404+00:00
-- url     : https://prove2.me/submissions/36b20707-e580-4964-bfe2-8c0ca7049da6

-- Sol generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_zLift_neighborSet
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








/-! ## The Petersen graph -/










/-! ## An infinite cubic Berge–Fulkerson graph over the Petersen graph -/










open Bridges.InfiniteCubicMatchings in
theorem solution(hK : IsCubic K) : IsCubic (zLift K vol hvol) := by
  intro p
  rw [zLift_neighborSet, Set.InjOn.ncard_image]
  · exact hK p.2
  · intro a _ b _ hab
    exact (Prod.ext_iff.mp hab).2
