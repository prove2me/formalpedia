-- Prove2me | Theorems.Thm_WorkbookSource_problem_3709
-- name    : WorkbookSource.problem_3709
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:21.566982+00:00
-- url     : https://prove2.me/theorems/04e709c8-3e8b-4d39-a0c9-e8d837561af9
-- title:
--   An exponential cancels a base-ten logarithm
-- statement:
--   The value of $ 10^{\log_{10}7}$ is:
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3709` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3709; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3709 : (10:ℝ)^(Real.logb 10 7) = 7  :=  by sorry
