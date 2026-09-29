-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
-- name    : Bridges_InfiniteCubicMatchingsPetersenLift
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:26:52.842456+00:00
-- url     : https://prove2.me/theorems/18c33355-203a-4ed0-8a43-f104f5a54e91
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsPetersenLift
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsPetersenLift`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsPetersenLift.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
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

namespace Bridges.InfiniteCubicMatchings

universe v

/-! ## ℤ-voltage lifts -/

section ZLift

variable {W : Type v} (K : SimpleGraph W) (vol : W → W → ℤ)

/-- The ℤ-voltage lift of `K`: vertices are pairs `(m, u)`, and `(m,u)` is adjacent to
`(m + vol u v, v)` for every neighbour `v` of `u`. -/
def zLift (hvol : ∀ u v : W, vol v u = -vol u v) : SimpleGraph (ℤ × W) where
  Adj p q := K.Adj p.2 q.2 ∧ q.1 = p.1 + vol p.2 q.2
  symm := by
    rintro ⟨m, u⟩ ⟨n, v⟩ ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    simp only at h2 ⊢
    rw [hvol u v, h2]
    ring
  loopless := ⟨by rintro ⟨m, u⟩ ⟨h1, -⟩; exact K.irrefl h1⟩

variable (hvol : ∀ u v : W, vol v u = -vol u v)







end ZLift

/-! ## The Petersen graph -/

/-- Neighbour lists of the Petersen graph: outer 5-cycle `0..4`, inner pentagram `5..9`,
spokes `i — i+5`. -/
def petersenNbr : Fin 10 → List (Fin 10)
  | 0 => [1, 4, 5] | 1 => [0, 2, 6] | 2 => [1, 3, 7] | 3 => [2, 4, 8] | 4 => [0, 3, 9]
  | 5 => [0, 7, 8] | 6 => [1, 8, 9] | 7 => [2, 5, 9] | 8 => [3, 5, 6] | 9 => [4, 6, 7]

/-- The Petersen graph. -/
def petersen : SimpleGraph (Fin 10) where
  Adj u v := v ∈ petersenNbr u
  symm := by intro a b; revert a b; decide
  loopless := ⟨by decide⟩

instance : DecidableRel petersen.Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ petersenNbr u))


/-- The six perfect matchings of the Petersen graph, given by their partner tables. -/
def petersenPM : Fin 6 → Fin 10 → Fin 10
  | 0 => ![1, 0, 3, 2, 9, 7, 8, 5, 6, 4]
  | 1 => ![1, 0, 7, 4, 3, 8, 9, 2, 5, 6]
  | 2 => ![4, 2, 1, 8, 0, 7, 9, 5, 3, 6]
  | 3 => ![4, 6, 3, 2, 0, 8, 1, 9, 5, 7]
  | 4 => ![5, 2, 1, 4, 3, 0, 8, 9, 6, 7]
  | 5 => ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]

/-- Each table indeed defines a perfect matching of the Petersen graph. -/
def petersenMatching (i : Fin 6) : PerfectMatching petersen where
  partner := petersenPM i
  isAdj := by revert i; decide
  invol := by revert i; decide




/-! ## An infinite cubic Berge–Fulkerson graph over the Petersen graph -/

/-- A nonzero voltage assignment on the Petersen graph: the edge `0 — 1` gets voltage `1`,
every other edge voltage `0`. -/
def petersenVol (u v : Fin 10) : ℤ := if u = 0 ∧ v = 1 then 1 else if u = 1 ∧ v = 0 then -1 else 0

theorem petersenVol_antisymm (u v : Fin 10) : petersenVol v u = -petersenVol u v := by
  revert u v
  decide

/-- The infinite ℤ-lift of the Petersen graph along `petersenVol`. -/
abbrev petersenLift : SimpleGraph (ℤ × Fin 10) := zLift petersen petersenVol petersenVol_antisymm






end Bridges.InfiniteCubicMatchings


