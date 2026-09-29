-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_Ladder_ladder_neighborSet
-- name    : Bridges.InfiniteCubicMatchings.Ladder.ladder_neighborSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:33.725694+00:00
-- url     : https://prove2.me/theorems/da9570dd-a6f0-456e-ad6b-53731aab27ff
-- title:
--   Ladder neighborSet
-- statement:
--   Formal statement of `Bridges.InfiniteCubicMatchings.Ladder.ladder_neighborSet` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.Ladder.ladder_neighborSet(p : ℤ × Bool) :
--       ladder.neighborSet p = {(p.1, !p.2), (p.1 + 1, p.2), (p.1 - 1, p.2)} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsLadder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsLadder.lean#L166

-- Thm stub generated from Bridges/InfiniteCubicMatchingsLadder.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
/-
# A concrete infinite cubic bridgeless graph satisfying all three conjectures

The doubly infinite ladder `L` on the vertex set `ℤ × Bool` (rungs `(n,b) — (n,¬b)` and rails
`(n,b) — (n+1,b)`) is an infinite, cubic, bridgeless graph.  We verify all of this formally
and exhibit an explicit proper 3-edge-colouring, which by
`ProperThreeEdgeColoring.bergeFulkerson` yields the Berge–Fulkerson property, hence also the
Fan–Raspaud and Máčajová–Škoviera properties.

This shows that the framework of `Bridges.InfiniteCubicMatchings` is not vacuous: it is
satisfied by a genuinely infinite cubic bridgeless graph.
-/

open Bridges.InfiniteCubicMatchings

open Ladder




/-! ## Three perfect matchings forming a proper 3-edge-colouring -/











/-! ## The ladder is an infinite, cubic, bridgeless graph -/

theorem Bridges.InfiniteCubicMatchings.Ladder.ladder_neighborSet(p : ℤ × Bool) :
    ladder.neighborSet p = {(p.1, !p.2), (p.1 + 1, p.2), (p.1 - 1, p.2)} := by sorry
