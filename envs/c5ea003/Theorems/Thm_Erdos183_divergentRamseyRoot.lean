-- Prove2me | Theorems.Thm_Erdos183_divergentRamseyRoot
-- name    : Erdos183.divergentRamseyRoot
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:19:09.158287+00:00
-- url     : https://prove2.me/theorems/14734603-1431-48f6-81b2-655a149e64ad
-- title:
--   The $k$-th root of the Ramsey number diverges
-- statement:
--   $$R_k^{1/k} \;\longrightarrow\; \infty \qquad (k \to \infty).$$
--
--   Here $R_k$ denotes the $k$-colour triangle Ramsey number `triangleRamseyNumber k`: the least $n$ such that every colouring of the edges of the complete graph $K_n$ with $k$ colours contains a monochromatic triangle. This is the qualitative statement Erdős asked about: the triangle Ramsey numbers grow faster than any fixed exponential. It follows from the explicit lower bound, whose base $\frac{1}{6e^{38}} k^{1/3}/\log k$ itself tends to infinity.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2999-L3033

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.divergentRamseyRoot :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by sorry
