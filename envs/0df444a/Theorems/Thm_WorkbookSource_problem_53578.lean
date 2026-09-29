-- Prove2me | Theorems.Thm_WorkbookSource_problem_53578
-- name    : WorkbookSource.problem_53578
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:15.395206+00:00
-- url     : https://prove2.me/theorems/4f937c94-3d0e-49c7-8c32-267317046b62
-- title:
--   The last four digits of an arithmetic expression
-- statement:
--   Find the last four digits of $\frac{2014\cdot 2015\cdot4029}{6}+\frac{3\cdot 2014\cdot 2015}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53578` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53578; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_53578 : (2014 * 2015 * 4029) / 6 + (3 * 2014 * 2015) / 2 ≡ 5330 [MOD 10^4]  :=  by sorry
