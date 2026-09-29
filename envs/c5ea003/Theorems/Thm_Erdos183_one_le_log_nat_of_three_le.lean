-- Prove2me | Theorems.Thm_Erdos183_one_le_log_nat_of_three_le
-- name    : Erdos183.one_le_log_nat_of_three_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:17:40.493481+00:00
-- url     : https://prove2.me/theorems/2de12042-58e1-413f-b9ef-e0f2b6f8befc
-- title:
--   Logarithm at least one from three onward
-- statement:
--   For every natural number $H \ge 3$ we have $1 \le \log H$. An elementary estimate, used to normalise the logarithmic factors in the quantitative bounds.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2327-L2333

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.one_le_log_nat_of_three_le (H : ℕ) (hH : 3 ≤ H) :
    1 ≤ Real.log (H : ℝ) := by sorry
