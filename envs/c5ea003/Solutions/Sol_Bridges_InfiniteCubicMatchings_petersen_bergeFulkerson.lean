-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.petersen_bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:10:55.684841+00:00
-- url     : https://prove2.me/submissions/2d97d7c2-9fa8-4141-a99d-91faab985be5

-- Sol generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
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
theorem solution: BergeFulkerson petersen := by
  refine ⟨petersenMatching, ?_⟩
  intro e
  induction e with
  | _ u w =>
    intro hE
    have hset : {i : Fin 6 | s(u, w) ∈ (petersenMatching i).edges}
        = {i : Fin 6 | petersenPM i u = w} := by
      ext i
      simp only [Set.mem_setOf_eq, PerfectMatching.mem_edges]
      rfl
    have key : ∀ a b : Fin 10, b ∈ petersenNbr a →
        (Finset.univ.filter (fun i : Fin 6 => petersenPM i a = b)).card = 2 := by decide
    rw [hset, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    exact key u w hE
