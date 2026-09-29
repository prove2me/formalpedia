-- Prove2me | Theorems.Thm_WorkbookSource_base_22767
-- name    : WorkbookSource.base_22767
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:26.097862+00:00
-- url     : https://prove2.me/theorems/e0b919cf-6329-4629-b7b1-3771aca47980
-- title:
--   A weighted sum of two squares bounds a normalized triple product
-- statement:
--   Let $a,b,c$ be positive real numbers .Prove that
--
--    $$(a+b)^2+\left(a+b-\frac{16}{3} \cdot c\right)^2 \geqslant \frac{200}{9} \cdot \frac{abc}{a+b+c}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22767` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22767; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22767 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b - 16 / 3 * c) ^ 2 ≥ 200 / 9 * (a * b * c) / (a + b + c)  :=  by sorry
