-- Prove2me | Theorems.Thm_Erdos180_quotientGraph_no_isolated
-- name    : Erdos180.quotientGraph_no_isolated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:09:04.653361+00:00
-- url     : https://prove2.me/theorems/7de84136-e5bb-4c28-a08c-d79067df52ae
-- title:
--   Admissible quotients have no isolated vertex
-- statement:
--   If a properly two-coloured graph has no isolated vertex and $f$ is a colour-respecting
--   identification, then the quotient graph has no isolated vertex either.
--
--   Applied to $J_0$ and $K_0$, this gives the same property for every member of $\mathcal{J}$ and
--   $\mathcal{K}$, which is what makes the padding argument of Proposition 4.3 available for the
--   whole family.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2722-L2733

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph

theorem Erdos180.quotientGraph_no_isolated
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v)
    (f : V → V) (hf : ColorRespecting color f) :
    ∀ u : Set.range f,
      ∃ v : Set.range f, (quotientGraph graph f).Adj u v := by sorry
