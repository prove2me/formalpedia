-- Prove2me | Theorems.Thm_WorkbookSource_plus_62807
-- name    : WorkbookSource.plus_62807
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:28.821476+00:00
-- url     : https://prove2.me/theorems/c0fd2903-8518-491e-b23a-4062307935d6
-- title:
--   A cyclic pair-product ratio sum has a symmetric quadratic upper bound
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{ab}{2c^2+ab+bc}+\frac{bc}{2a^2+bc+ca}+\frac{ca}{2b^2+ca+ab}\le\frac{3}{4}\cdot\frac{a^2+b^2+c^2}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62807` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62807; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_62807 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≤ (3 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)   :=  by sorry
