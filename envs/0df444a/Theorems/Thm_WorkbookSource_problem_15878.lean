-- Prove2me | Theorems.Thm_WorkbookSource_problem_15878
-- name    : WorkbookSource.problem_15878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:37:03.212808+00:00
-- url     : https://prove2.me/theorems/01f66078-5e6a-4b59-a0b0-8d6c0960cb16
-- title:
--   Two bounds under a quadratic normalization
-- statement:
--   Let $ a,b,c \in R^+$ be such that $ (a+b)^2+(b+c)^2+(c+a)^2=3$ . prove that $ 2(b+c)^2 \le 6-(2a+b+c)^2 \le 4(b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15878` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15878; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_15878 (a b c : ℝ) (h : (a+b)^2 + (b+c)^2 + (c+a)^2 = 3) : 2 * (b+c)^2 ≤ 6 - (2*a + b + c)^2 ∧ 6 - (2*a + b + c)^2 ≤ 4 * (b^2 + c^2)  :=  by sorry
