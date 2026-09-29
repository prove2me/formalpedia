-- Prove2me | Theorems.Thm_WorkbookSource_base_49525
-- name    : WorkbookSource.base_49525
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:28.280144+00:00
-- url     : https://prove2.me/theorems/e1e30e2c-4418-431d-b7a2-6a3466b866c3
-- title:
--   A reciprocal sum lower bound at fixed sum six
-- statement:
--   Let $ a,b,c$ be positive real numbers having sum $ 6.$ Prove that $ \frac {1}{a} + \frac {1}{b} + \frac {1}{c} \ge \frac {21}{abc + 6}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49525` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49525; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49525 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6) : 1 / a + 1 / b + 1 / c ≥ 21 / (a * b * c + 6)  :=  by sorry
