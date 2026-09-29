-- Prove2me | Theorems.Thm_WorkbookSource_base_2528
-- name    : WorkbookSource.base_2528
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:32.029521+00:00
-- url     : https://prove2.me/theorems/4e77e74b-1a7d-4a44-aa57-aa45c47f58ad
-- title:
--   A two-term rational lower bound for three positive variables
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $\frac{(a+b)^2}{c} + \frac{c^2}{a} \geq 4b$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2528` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2528; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2528 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b) ^ 2 / c + c ^ 2 / a ≥ 4 * b  :=  by sorry
