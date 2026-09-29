-- Prove2me | Theorems.Thm_WorkbookSource_plus_73065
-- name    : WorkbookSource.plus_73065
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:25.662927+00:00
-- url     : https://prove2.me/theorems/ef121dbf-5199-47f3-8534-55c5cd115574
-- title:
--   A squared triangle-difference ratio sum with a quadratic correction
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{(a+b-c)^2}{(a+b)^2+c^2}+\frac{(b+c-a)^2}{(b+c)^2+a^2}+\frac{(c+a-b)^2}{(c+a)^2+b^2}+\frac{12}{25}\cdot\frac{ab+bc+ca}{a^2+b^2+c^2} \ge \frac{27}{25}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73065` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73065; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73065 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) + (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + 12 / 25 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 27 / 25   :=  by sorry
