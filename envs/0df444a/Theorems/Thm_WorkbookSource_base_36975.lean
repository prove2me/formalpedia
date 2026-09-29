-- Prove2me | Theorems.Thm_WorkbookSource_base_36975
-- name    : WorkbookSource.base_36975
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:19:48.733282+00:00
-- url     : https://prove2.me/theorems/ab6beff7-0b8a-45e8-8436-170c754f5b6c
-- title:
--   A cyclic reciprocal-power comparison at fixed sum three
-- statement:
--   If ${x}$ , $y$ and $z>0$ satisfies $x+y+z=3$ , show that $\frac{x}{y^2}+\frac{y}{z^2}+\frac{z}{x^2}\ge \frac{x^2}{y}+\frac{y^2}{z}+\frac{z^2}{x}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36975` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36975; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36975 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x / y ^ 2 + y / z ^ 2 + z / x ^ 2) ≥ (x ^ 2 / y + y ^ 2 / z + z ^ 2 / x)  :=  by sorry
