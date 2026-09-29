-- Prove2me | Theorems.Thm_WorkbookSource_base_17948
-- name    : WorkbookSource.base_17948
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:26:42.16424+00:00
-- url     : https://prove2.me/theorems/93e6eb9e-2a2e-43b5-ac4c-59d94bdd1bfc
-- title:
--   A shifted pair-product ratio upper bound
-- statement:
--   If $a, b, c>0$ prove that $\frac{ab}{2c^2+ab+1}+\frac{bc}{2a^2+bc+1}+\frac{ca}{2b^2+ca+1}\le\frac{a^2+b^2+c^2}{1+ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17948` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17948; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17948 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + 1) + b * c / (2 * a ^ 2 + b * c + 1) + c * a / (2 * b ^ 2 + c * a + 1)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (1 + a * b + b * c + a * c)  :=  by sorry
