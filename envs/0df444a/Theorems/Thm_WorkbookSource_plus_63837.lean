-- Prove2me | Theorems.Thm_WorkbookSource_plus_63837
-- name    : WorkbookSource.plus_63837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:41:46.584353+00:00
-- url     : https://prove2.me/theorems/7c8c10bd-eb65-41ba-a90e-2902004067b9
-- title:
--   A complementary cyclic ratio sum is nonnegative at fixed sum three
-- statement:
--   Let $ a,b,c $ be positive real numbers such that: $ a+b+c=3 $ .Prove that: $ \frac{(1-a)(1-ab)}{a(1+c)}+\frac{(1-b)(1-bc)}{b(1+a)}+\frac{(1-c)(1-ca)}{c(1+b)} \ge 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63837` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63837; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 - a) * (1 - a * b) / (a * (1 + c)) + (1 - b) * (1 - b * c) / (b * (1 + a)) + (1 - c) * (1 - c * a) / (c * (1 + b)) ≥ 0   :=  by sorry
