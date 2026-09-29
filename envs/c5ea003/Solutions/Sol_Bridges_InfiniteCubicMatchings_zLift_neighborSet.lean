-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.zLift_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:45:29.01016+00:00
-- url     : https://prove2.me/submissions/9dba52e8-c295-44c9-b47a-2a17e9d46b11

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
theorem solution(p : ℤ × W) :
    (zLift K vol hvol).neighborSet p = (fun y => (p.1 + vol p.2 y, y)) '' K.neighborSet p.2 := by
  ext ⟨n, v⟩
  simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨v, h1, by simp only at h2; rw [h2]⟩
  · rintro ⟨y, hy, heq⟩
    rw [Prod.ext_iff] at heq
    obtain ⟨heq1, heq2⟩ := heq
    simp only at heq1 heq2
    subst heq2
    exact ⟨hy, by simp only; rw [heq1]⟩
