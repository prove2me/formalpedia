-- Prove2me | Theorems.Thm_WorkbookSource_problem_12814
-- name    : WorkbookSource.problem_12814
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:18.761443+00:00
-- url     : https://prove2.me/theorems/f349109a-aade-4b8b-8810-917759c4bc67
-- title:
--   A sharp bound with a fixed sum
-- statement:
--   If $x,y\ge0$ and $x+y=1$, then $$x^2+y^2+x^2y^2\ge\frac9{16}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12814` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12814; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_12814 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) : x^2 + y^2 + x^2 * y^2 ≥ 9 / 16  :=  by sorry
