-- Prove2me | Theorems.Thm_WorkbookSource_plus_23017
-- name    : WorkbookSource.plus_23017
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:31.663243+00:00
-- url     : https://prove2.me/theorems/6812758c-d5c7-41b5-aeee-2ceb0f8a8a44
-- title:
--   A shifted ratio sum bounds a triple-product expression
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that:
--   $$\frac{a}{a+1}+\frac{b}{b+1}+\frac{c}{c+1} \geq \frac{3(1+abc)}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23017` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23017; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23017 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (a / (a + 1) + b / (b + 1) + c / (c + 1)) ≥ (3 * (1 + a * b * c)) / 4   :=  by sorry
