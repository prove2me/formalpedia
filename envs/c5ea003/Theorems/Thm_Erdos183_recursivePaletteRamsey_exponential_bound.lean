-- Prove2me | Theorems.Thm_Erdos183_recursivePaletteRamsey_exponential_bound
-- name    : Erdos183.recursivePaletteRamsey_exponential_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:17:00.76141+00:00
-- url     : https://prove2.me/theorems/3d416ee7-f2e8-4c67-b821-6ca9d7ee1124
-- title:
--   Exponential Ramsey lower bound from the palette recursion
-- statement:
--   For $2 \le H$, $2 \le a$ and $\log H \le a$, writing $m = H \cdot (a \cdot \text{saturatedMatrixRows}(H))$ for the number of colours,
--
--   $$\left(\frac{H}{e^{4}}\right)^{m} \;\le\; R_{m}.$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. Iterating the palette stage and applying the triangle-free lower-bound criterion converts the construction into this exponential lower bound, with the base $H/e^4$ improving as $H$ grows.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2159-L2239

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.recursivePaletteRamsey_exponential_bound (H a : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a)
    (hloga : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by sorry
