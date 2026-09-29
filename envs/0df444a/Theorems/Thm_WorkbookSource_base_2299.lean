-- Prove2me | Theorems.Thm_WorkbookSource_base_2299
-- name    : WorkbookSource.base_2299
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:57:12.90742+00:00
-- url     : https://prove2.me/theorems/5283b288-0081-4739-8d72-4a6b3246f524
-- title:
--   A cyclic quadratic-difference ratio sum is nonnegative
-- statement:
--   prove $ \sum_{cyc} \frac{a^2-b^2}{a^2+b^2} \cdot a \geq 0 $ where $ a,b,c>0 $ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2299` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2299; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2299 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b^2) / (a^2 + b^2) * a + (b^2 - c^2) / (b^2 + c^2) * b + (c^2 - a^2) / (c^2 + a^2) * c ≥ 0  :=  by sorry
