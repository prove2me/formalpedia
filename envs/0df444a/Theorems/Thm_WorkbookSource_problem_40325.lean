-- Prove2me | Theorems.Thm_WorkbookSource_problem_40325
-- name    : WorkbookSource.problem_40325
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:23.920353+00:00
-- url     : https://prove2.me/theorems/69523578-eea4-477d-81f8-7eaf4860d593
-- title:
--   A five-variable quadratic inequality over the reals
-- statement:
--   Prove that $2\sum_{i=1}^{5} r_i^2 \ge \sum_{1\le i < j \le 5} r_ir_j$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40325` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. This version covers all real inputs; the related five-variable records plus_72847 and plus_10229 assume positivity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40325; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_40325 (r : ℕ → ℝ) : 2 * (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 + r 4 ^ 2 + r 5 ^ 2) ≥ r 1 * r 2 + r 1 * r 3 + r 1 * r 4 + r 1 * r 5 + r 2 * r 3 + r 2 * r 4 + r 2 * r 5 + r 3 * r 4 + r 3 * r 5 + r 4 * r 5  :=  by sorry
