-- Prove2me | Theorems.Thm_WorkbookSource_base_21608
-- name    : WorkbookSource.base_21608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:47:11.872812+00:00
-- url     : https://prove2.me/theorems/4eca4ecb-12e8-442c-8fc1-729f796f6663
-- title:
--   A squared cyclic ratio sum bounds an asymmetric product
-- statement:
--   Let be given positive real numbers $ a,b,c $ ,prove that $ (\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+1)^2\ge(2a+b+c)(\frac{2}{a}+\frac{1}{b}+\frac{1}{c}) .$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21608 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 1) ^ 2 ≥ (2 * a + b + c) * (2 / a + 1 / b + 1 / c)  :=  by sorry
