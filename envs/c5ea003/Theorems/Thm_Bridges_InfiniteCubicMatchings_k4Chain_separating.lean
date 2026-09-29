-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_k4Chain_separating
-- name    : Bridges.InfiniteCubicMatchings.k4Chain_separating
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:27:52.462078+00:00
-- url     : https://prove2.me/theorems/b8256787-aece-4c57-b2c6-5124470babaf
-- title:
--   Apart from the edge `(m,3) — (m+1,0)`, no edge of the chain joins a level `≤ m` to a level
-- statement:
--   Apart from the edge `(m,3) — (m+1,0)`, no edge of the chain joins a level `≤ m` to a level
--   `≥ m+1`.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.k4Chain_separating(m : ℤ) (a b : ℤ × Fin 4)
--       (h : (k4Chain \ SimpleGraph.fromEdgeSet {s((m, 3), (m + 1, 0))}).Adj a b) :
--       (a ∈ leftLevels m ↔ b ∈ leftLevels m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsBridged.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsBridged.lean#L135

-- Thm stub generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
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

open Bridges.InfiniteCubicMatchings

universe u

/-! ## A separation criterion for non-reachability -/

variable {V : Type u}



/-! ## `K₄` and its three perfect matchings -/








/-! ## Unrolling one edge of `K₄` along ℤ -/









/-! ## The chain has infinitely many bridges -/

theorem Bridges.InfiniteCubicMatchings.k4Chain_separating(m : ℤ) (a b : ℤ × Fin 4)
    (h : (k4Chain \ SimpleGraph.fromEdgeSet {s((m, 3), (m + 1, 0))}).Adj a b) :
    (a ∈ leftLevels m ↔ b ∈ leftLevels m) := by sorry
