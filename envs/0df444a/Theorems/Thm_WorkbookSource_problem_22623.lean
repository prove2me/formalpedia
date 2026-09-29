-- Prove2me | Theorems.Thm_WorkbookSource_problem_22623
-- name    : WorkbookSource.problem_22623
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:32.656983+00:00
-- url     : https://prove2.me/theorems/fe1fd575-fd4a-48c6-b597-9d25b473b88f
-- title:
--   A cross-product identity for logarithm quotients
-- statement:
--   Prove the logarithmic identity: $\left(\log_{a}b\right)\left(\log_{c}d\right)=\left(\log_{a}d\right)\left(\log_cb\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22623` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22623; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_22623 (a b c d : ℝ) : (Real.log b / Real.log a) * (Real.log d / Real.log c) = (Real.log d / Real.log a) * (Real.log b / Real.log c)  :=  by sorry
