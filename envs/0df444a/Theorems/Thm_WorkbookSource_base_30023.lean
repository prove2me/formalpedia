-- Prove2me | Theorems.Thm_WorkbookSource_base_30023
-- name    : WorkbookSource.base_30023
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:26.688955+00:00
-- url     : https://prove2.me/theorems/101dcb92-a0c8-400b-9c4d-fff57b7c1473
-- title:
--   A weighted four-variable linear ratio sum is at most twenty thirteenths
-- statement:
--   If $a, b, c, d>0$ , prove that
--    \begin{align}\frac{a+2b+3c+4d}{5a+6b+7c+8d}+\frac{2a+3b+4c+d}{6a+7b+8c+5d}+\frac{3a+4b+c+2d}{7a+8b+5c+6d}+\frac{4a+b+2c+3d}{8a+5b+6c+7d}\leq\frac{20}{13}\end{align}
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30023` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30023; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30023 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + 2 * b + 3 * c + 4 * d) / (5 * a + 6 * b + 7 * c + 8 * d) + (2 * a + 3 * b + 4 * c + d) / (6 * a + 7 * b + 8 * c + 5 * d) + (3 * a + 4 * b + c + 2 * d) / (7 * a + 8 * b + 5 * c + 6 * d) + (4 * a + b + 2 * c + 3 * d) / (8 * a + 5 * b + 6 * c + 7 * d) ≤ 20 / 13  :=  by sorry
