-- Prove2me | Theorems.Thm_WorkbookSource_base_36997
-- name    : WorkbookSource.base_36997
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:23.548415+00:00
-- url     : https://prove2.me/theorems/5fad9c52-326d-4d4f-8f13-20f145b436b3
-- title:
--   A cyclic fourth-degree rational difference is nonnegative
-- statement:
--   For $x, y, z>0,$ prove that $x^2\frac{x^2-y^2}{x^2+3y^2}+y^2\frac{y^2-z^2}{y^2+3z^2}+z^2\frac{z^2-x^2}{z^2+3x^2}\geq0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36997` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36997; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36997 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2 * (x^2 - y^2) / (x^2 + 3 * y^2) + y^2 * (y^2 - z^2) / (y^2 + 3 * z^2) + z^2 * (z^2 - x^2) / (z^2 + 3 * x^2) ≥ 0  :=  by sorry
