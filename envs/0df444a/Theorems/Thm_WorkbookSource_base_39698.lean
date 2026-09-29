-- Prove2me | Theorems.Thm_WorkbookSource_base_39698
-- name    : WorkbookSource.base_39698
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:38.917866+00:00
-- url     : https://prove2.me/theorems/f2e1141e-f5e6-46c4-9312-968a9a4b9c96
-- title:
--   A squared cyclic quadratic ratio sum bounds cubic ratios
-- statement:
--   Let $a,b,c$ be positive numbers. Prove that:
--
--    $(\frac{a^{2}}{b}+\frac{b^{2}}{c}+\frac{c^{2}}{a})^{2}\ge 3(\frac{a^{3}}{b}+\frac{b^{3}}{c}+\frac{c^{3}}{a})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39698` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39698; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39698 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a)^2 ≥ 3 * (a^3 / b + b^3 / c + c^3 / a)  :=  by sorry
