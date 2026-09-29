-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_Ladder_cutEdgesSet_leftPlus
-- name    : Bridges.InfiniteCubicMatchings.Ladder.cutEdgesSet_leftPlus
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:41.880064+00:00
-- url     : https://prove2.me/theorems/4afb1a1b-7864-4218-9d3d-4066d4eed717
-- title:
--   The three edges of the cut of `leftPlus`.
-- statement:
--   The three edges of the cut of `leftPlus`.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.Ladder.cutEdgesSet_leftPlus:
--       cutEdgesSet ladder leftPlus =
--         {s(((0 : ℤ), true), ((1 : ℤ), true)), s(((1 : ℤ), false), ((1 : ℤ), true)),
--           s(((1 : ℤ), false), ((2 : ℤ), false))} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsParitySharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsParitySharp.lean#L64

-- Thm stub generated from Bridges/InfiniteCubicMatchingsParitySharp.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
import Definitions.Def_Bridges_InfiniteCubicMatchingsParitySharp
/-
# Sharpness of the parity lemma in the infinite setting

The parity lemma `PerfectMatching.card_inter_cutEdges_odd` says that a perfect matching meets
every edge cut of odd size **with a finite side** in an odd number of edges.  In finite graphs
the finiteness assumption is vacuous.  Here we prove that in infinite graphs it cannot be
dropped: the infinite ladder has an edge cut of size `3` (odd), both sides of which are
infinite, that is *disjoint* from a perfect matching.

This is the fundamental new phenomenon of the infinite theory: parity arguments are only
available for cuts with a finite side, which is why `IsOddCut` is defined via a `Finset`.
-/

open Bridges.InfiniteCubicMatchings

open Ladder

theorem Bridges.InfiniteCubicMatchings.Ladder.cutEdgesSet_leftPlus:
    cutEdgesSet ladder leftPlus =
      {s(((0 : ℤ), true), ((1 : ℤ), true)), s(((1 : ℤ), false), ((1 : ℤ), true)),
        s(((1 : ℤ), false), ((2 : ℤ), false))} := by sorry
