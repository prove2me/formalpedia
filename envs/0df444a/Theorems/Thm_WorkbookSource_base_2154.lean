-- Prove2me | Theorems.Thm_WorkbookSource_base_2154
-- name    : WorkbookSource.base_2154
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:30.387627+00:00
-- url     : https://prove2.me/theorems/9991d47f-36fa-4be2-8205-1c684d1f7756
-- title:
--   A cyclic rational inequality in two positive variables
-- statement:
--   Given $a=x^2$, $b=y^2$ where $x>0$ and $y>0$, prove that $\dfrac{x^2}{y^2}+\dfrac{y^2}{(x+y)^2}+\dfrac{(x+y)^2}{x^2}\geq\dfrac{10(x^4+y^4+(x+y)^4)}{(x^2+y^2+(x+y)^2)^2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2154` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2154; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2154 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^2 / y^2 + y^2 / (x + y)^2 + (x + y)^2 / x^2) ≥ (10 * (x^4 + y^4 + (x + y)^4)) / (x^2 + y^2 + (x + y)^2)^2  :=  by sorry
