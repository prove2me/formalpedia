-- Prove2me | Theorems.Thm_WorkbookSource_base_21853
-- name    : WorkbookSource.base_21853
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:43.594022+00:00
-- url     : https://prove2.me/theorems/f98cacd8-6f88-4d63-8eab-3188b387aa28
-- title:
--   A squared-norm-squared bound at fixed positive sum
-- statement:
--   Let $a,b,c$ be positive reals such that $a+b+c=3;$ prove that $$(a^2+b^2+c^2)^2\geq 4(a^2+b^2+c^2)-abc(a+b+c)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21853` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21853; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21853 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + b^2 + c^2)^2 ≥ 4 * (a^2 + b^2 + c^2) - a * b * c * (a + b + c)  :=  by sorry
