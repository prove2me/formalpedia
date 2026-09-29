-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_k4Chain_bergeFulkerson
-- name    : Bridges.InfiniteCubicMatchings.k4Chain_bergeFulkerson
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:27:49.960634+00:00
-- url     : https://prove2.me/theorems/710d63fb-224a-41b9-8b20-3d5bfe62eef8
-- title:
--   The chain satisfies Berge–Fulkerson, even though it has a bridge.
-- statement:
--   **The chain satisfies Berge–Fulkerson**, even though it has a bridge.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.k4Chain_bergeFulkerson: BergeFulkerson k4Chain := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsBridged.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsBridged.lean#L118

-- Thm stub generated from Bridges/InfiniteCubicMatchingsBridged.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
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

theorem Bridges.InfiniteCubicMatchings.k4Chain_bergeFulkerson: BergeFulkerson k4Chain := by sorry
