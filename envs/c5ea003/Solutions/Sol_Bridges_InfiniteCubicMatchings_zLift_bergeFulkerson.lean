-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.zLift_bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:45:28.429843+00:00
-- url     : https://prove2.me/submissions/5474e1e2-1ff3-42d0-865c-d055e7896b0c

-- Sol generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
import Theorems.Thm_Bridges_InfiniteCubicMatchings_BergeFulkerson_of_covering
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

/-- The projection to the second coordinate is a covering map from the lift to the base. -/
theorem isLocalIsoAt_zLift (p : ℤ × W) : IsLocalIsoAt (zLift K vol hvol) K Prod.snd p where
  adj := fun _ h => h.1
  inj := by
    rintro ⟨n, v⟩ ⟨n', v'⟩ ⟨-, h2⟩ ⟨-, h4⟩ hv
    simp only at hv h2 h4
    subst hv
    simp only [Prod.mk.injEq, and_true]
    rw [h2, h4]
  surj := fun y hy => ⟨(p.1 + vol p.2 y, y), ⟨hy, rfl⟩, rfl⟩







/-! ## The Petersen graph -/










/-! ## An infinite cubic Berge–Fulkerson graph over the Petersen graph -/










open Bridges.InfiniteCubicMatchings in
theorem solution(hK : BergeFulkerson K) : BergeFulkerson (zLift K vol hvol) :=
  BergeFulkerson.of_covering Prod.snd (isLocalIsoAt_zLift K vol hvol) hK
