-- Prove2me | Theorems.Thm_WorkbookSource_base_51867
-- name    : WorkbookSource.base_51867
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:48.352984+00:00
-- url     : https://prove2.me/theorems/d92af867-9290-4d9c-99ae-4bb297363eec
-- title:
--   A shifted pair-product ratio upper bound at fixed sum three
-- statement:
--   Prove that $ \frac {ab}{7 + 2c^2} + \frac {bc}{7 + 2a^2} + \frac {ca}{7 + 2b^2} \le \frac {1}{3}$ for all $ a,b,c > 0: a + b + c = 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51867` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51867; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51867 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b) / (7 + 2 * c ^ 2) + (b * c) / (7 + 2 * a ^ 2) + (c * a) / (7 + 2 * b ^ 2) ≤ 1 / 3  :=  by sorry
