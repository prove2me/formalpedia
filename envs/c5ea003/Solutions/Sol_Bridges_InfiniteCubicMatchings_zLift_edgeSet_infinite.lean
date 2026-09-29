-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.zLift_edgeSet_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:52:04.835971+00:00
-- url     : https://prove2.me/submissions/3727dd6f-9231-4f1a-9aa3-eebf2a3d57c7

-- Sol generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
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








/-! ## The Petersen graph -/










/-! ## An infinite cubic Berge–Fulkerson graph over the Petersen graph -/










open Bridges.InfiniteCubicMatchings in
theorem solution{u v : W} (huv : K.Adj u v) :
    ((zLift K vol hvol).edgeSet).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℤ => s((n, u), (n + vol u v, v)))
  · intro n m hnm
    rcases Sym2.eq_iff.mp hnm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact congrArg Prod.fst h1
    · exact absurd (congrArg Prod.snd h1 : u = v) (K.ne_of_adj huv)
  · intro n
    exact ⟨huv, rfl⟩
