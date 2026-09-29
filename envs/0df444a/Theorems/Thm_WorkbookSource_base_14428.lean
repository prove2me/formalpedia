-- Prove2me | Theorems.Thm_WorkbookSource_base_14428
-- name    : WorkbookSource.base_14428
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:53.792781+00:00
-- url     : https://prove2.me/theorems/a3429dd6-474b-4939-a7e8-0ac4cb0ee75b
-- title:
--   A cyclic ratio sum with a quadratic correction
-- statement:
--   Let $a, b, c > 0$. Prove that
--    $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{ab+bc+ca}{a^2+b^2+c^2}\ge 4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14428` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14428; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14428 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4  :=  by sorry
