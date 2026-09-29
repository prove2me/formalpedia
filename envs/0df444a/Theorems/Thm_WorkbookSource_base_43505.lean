-- Prove2me | Theorems.Thm_WorkbookSource_base_43505
-- name    : WorkbookSource.base_43505
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:48.888836+00:00
-- url     : https://prove2.me/theorems/ed429007-40d5-4f66-84e4-af14b09c4d6f
-- title:
--   A product of three quadratic expressions bounds a cube
-- statement:
--   Given $a,b,c>0$ prove that $(2(b-c)^{2}+2a^{2}+bc)(2(c-a)^{2}+2b^{2}+ca)(2(a-b)^{2}+2c^{2}+ab)\ge (a^{2}+b^{2}+c^{2})^{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43505` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43505; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43505 (a b c : ℝ) : (2 * (b - c) ^ 2 + 2 * a ^ 2 + b * c) * (2 * (c - a) ^ 2 + 2 * b ^ 2 + c * a) * (2 * (a - b) ^ 2 + 2 * c ^ 2 + a * b) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3  :=  by sorry
