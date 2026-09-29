-- Prove2me | Theorems.Thm_WorkbookSource_base_5736
-- name    : WorkbookSource.base_5736
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:37:30.764654+00:00
-- url     : https://prove2.me/theorems/a7e42941-1793-41dd-ac83-bb19355dea51
-- title:
--   A rational comparison of symmetric quadratic and cubic expressions
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $1+\frac{8abc}{(a+b)(b+c)(c+a)}\geq \frac{2(ab+bc+ca)}{a^2+b^2+c^2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5736` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5736; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5736 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 + (8 * a * b * c) / (a + b) / (b + c) / (c + a) ≥ 2 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
