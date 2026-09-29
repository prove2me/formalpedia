-- Prove2me | Theorems.Thm_WorkbookSource_problem_48897
-- name    : WorkbookSource.problem_48897
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:35.656991+00:00
-- url     : https://prove2.me/theorems/7ca92872-5158-4128-85ac-1853964d7426
-- title:
--   A positive sum rules out three negative summands
-- statement:
--   the roots are $\frac{a+b+c\pm \sqrt{\Delta}}{2}$ have the real part $a+b+c$ which is equal to $\alpha$ and greatest than $0$ . So $a,b,c$ cannot be three negative numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48897` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48897; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_48897 (a b c : ℝ) (habc : a + b + c > 0) : ¬ (a < 0 ∧ b < 0 ∧ c < 0)  :=  by sorry
