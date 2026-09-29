-- Prove2me | Theorems.Thm_Erdos183_forcesMonochromaticTriangle_zero
-- name    : Erdos183.forcesMonochromaticTriangle_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:15:33.091273+00:00
-- url     : https://prove2.me/theorems/9ef7df58-d23f-4b0d-94f2-c0ec96b02662
-- title:
--   Two vertices force a monochromatic triangle with zero colours
-- statement:
--   With no colours available, a complete graph on $2$ vertices already forces a monochromatic triangle, vacuously: there is no edge-colouring of $K_2$ by the empty set of colours that avoids one, because $K_2$ has an edge to colour and no colour to give it.
--
--   This is the base case of the recursion that bounds $R_k$ from above.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L236-L239

import Definitions.Def_erdos183_core
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.forcesMonochromaticTriangle_zero :
    ForcesMonochromaticTriangle 2 0 := by sorry
