-- Prove2me | Theorems.Thm_WorkbookSource_problem_26366
-- name    : WorkbookSource.problem_26366
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:40.379124+00:00
-- url     : https://prove2.me/theorems/7f14c640-9c8a-4f5b-8109-60d53f5d055a
-- title:
--   A symmetric product inequality
-- statement:
--   Let $x, y\in R, a,b>0$ . Prove that $$(ax+by)(bx+ay) \ge (a+b)^2xy.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26366` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26366; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_26366 (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a * x + b * y) * (b * x + a * y) ≥ (a + b) ^ 2 * x * y  :=  by sorry
