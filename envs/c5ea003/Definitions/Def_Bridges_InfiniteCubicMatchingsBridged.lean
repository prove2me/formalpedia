-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
-- name    : Bridges_InfiniteCubicMatchingsBridged
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:23.103853+00:00
-- url     : https://prove2.me/theorems/b663ebe7-1f97-42f5-8be2-e8eec77b871f
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsBridged
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsBridged`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsBridged.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
/-
# Bridges are *not* an obstruction in the infinite setting

For finite cubic graphs, a bridge kills all three conjectures: the bridge is a one-element odd
cut, and `not_bergeFulkerson_of_oddCut_singleton` shows the same in the infinite setting
*provided one side of the cut is finite*.  This file shows that the finiteness proviso is
essential, by exhibiting

  `k4Chain` : an infinite cubic graph, every level of which is a copy of `K₄` with one edge
  "unrolled" along ℤ,

which

* is cubic (`k4Chain_isCubic`),
* satisfies Berge–Fulkerson, Fan–Raspaud and Máčajová–Škoviera
  (`k4Chain_bergeFulkerson`, …), and yet
* **has a bridge** (`k4Chain_isBridge`): in fact every edge joining level `m` to level `m+1`
  is one, so it has infinitely many bridges (`k4Chain_bridges_infinite`).

Hence, unlike in the finite case, bridgelessness is not a necessary condition for any of the
three properties once the graph is infinite: the two sides of the offending cut are infinite,
so the parity argument behind the finite obstruction has nothing to bite on.
-/

namespace Bridges.InfiniteCubicMatchings

universe u

/-! ## A separation criterion for non-reachability -/

variable {V : Type u}



/-! ## `K₄` and its three perfect matchings -/

/-- The complete graph on four vertices. -/
def k4 : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel k4.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))


/-- The three perfect matchings of `K₄`, as partner tables. -/
def k4PM : Fin 3 → Fin 4 → Fin 4
  | 0 => ![1, 0, 3, 2]
  | 1 => ![2, 3, 0, 1]
  | 2 => ![3, 2, 1, 0]

/-- Each table is a perfect matching of `K₄`. -/
def k4Matching (i : Fin 3) : PerfectMatching k4 where
  partner := k4PM i
  isAdj := by revert i; decide
  invol := by revert i; decide



/-! ## Unrolling one edge of `K₄` along ℤ -/

/-- The voltage assignment giving the edge `3 — 0` of `K₄` voltage `1`, all other edges
voltage `0`. -/
def k4Vol (u v : Fin 4) : ℤ := if u = 3 ∧ v = 0 then 1 else if u = 0 ∧ v = 3 then -1 else 0

theorem k4Vol_antisymm (u v : Fin 4) : k4Vol v u = -k4Vol u v := by
  revert u v
  decide

/-- The infinite ℤ-voltage lift of `K₄` along `k4Vol`: an infinite chain of `K₄`-blocks, each
joined to the next by a single edge. -/
abbrev k4Chain : SimpleGraph (ℤ × Fin 4) := zLift k4 k4Vol k4Vol_antisymm






/-! ## The chain has infinitely many bridges -/

/-- Levels `≤ m` of the chain. -/
def leftLevels (m : ℤ) : Set (ℤ × Fin 4) := {p | p.1 ≤ m}





end Bridges.InfiniteCubicMatchings


