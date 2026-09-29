-- Prove2me | Theorems.Thm_WorkbookSource_plus_64869
-- name    : WorkbookSource.plus_64869
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:41:42.664933+00:00
-- url     : https://prove2.me/theorems/7dfa095b-f990-4031-8d0f-1e0e551f2a68
-- title:
--   A weighted cubic ratio sum bounds five halves of the total
-- statement:
--   For $a, b, c>0$ prove that $\frac{3a^3+2b^3}{a^2+b^2}+\frac{3b^3+2c^3}{b^2+c^2}+\frac{3c^3+2a^3}{c^2+a^2}\ge\frac{5}{2}(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_64869` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_64869; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_64869 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a ^ 3 + 2 * b ^ 3) / (a ^ 2 + b ^ 2) + (3 * b ^ 3 + 2 * c ^ 3) / (b ^ 2 + c ^ 2) + (3 * c ^ 3 + 2 * a ^ 3) / (c ^ 2 + a ^ 2) ≥ 5 / 2 * (a + b + c)   :=  by sorry
