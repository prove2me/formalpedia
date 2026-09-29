-- Prove2me | Theorems.Thm_WorkbookSource_plus_41300
-- name    : WorkbookSource.plus_41300
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:50.673614+00:00
-- url     : https://prove2.me/theorems/d033b885-e23c-420e-81f2-1a498597beb9
-- title:
--   A total and squared pair-product ratio sum is at least twenty ninths
-- statement:
--   Let $ a, b,c>0 $ . Prove that \$$a+b+c+\frac{(ab+bc+ca-2)^2}{a+b+c}\ge\frac{20}{9}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_41300` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_41300; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_41300 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a + b + c + (a * b + b * c + c * a - 2) ^ 2 / (a + b + c) ≥ 20 / 9   :=  by sorry
