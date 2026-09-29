-- Prove2me | Theorems.Thm_WorkbookSource_problem_5159
-- name    : WorkbookSource.problem_5159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:21.519416+00:00
-- url     : https://prove2.me/theorems/d2f8d7fb-8a73-4f5b-88e3-22cacd5d13d8
-- title:
--   A sum bound under a pairwise-product constraint
-- statement:
--   For real $a,b,c$ with $ab+ac+bc=3$, $$a^2+b^2+c^2+5(ab+bc+ca)\ge6(a+b+c).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5159` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5159; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_5159 (a b c: ℝ) (hab : a * b + a * c + b * c = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 5 * (a * b + b * c + c * a) ≥ 6 * (a + b + c)  :=  by sorry
