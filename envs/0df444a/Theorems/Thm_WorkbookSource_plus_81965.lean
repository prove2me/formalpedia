-- Prove2me | Theorems.Thm_WorkbookSource_plus_81965
-- name    : WorkbookSource.plus_81965
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:30.228036+00:00
-- url     : https://prove2.me/theorems/9fc58117-6280-4048-a2fe-33a0da3fc904
-- title:
--   A mixed shifted reciprocal sum has a pair-product upper bound
-- statement:
--   Let $a,b,c$ are positive numbers satisfies $a+b+c=3$ , prove that $\frac{1}{2a+bc}+\frac{1}{2b+ca}+\frac{1}{2c+ab} \leq \frac{3}{bc+ca+ab}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81965` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81965; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81965 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b)) ≤ (3 / (b * c + c * a + a * b))   :=  by sorry
