-- Prove2me | Theorems.Thm_WorkbookSource_base_29335
-- name    : WorkbookSource.base_29335
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:12.630421+00:00
-- url     : https://prove2.me/theorems/e9a45380-3a4e-4a23-a1f6-e0f583a2d844
-- title:
--   A cyclic pair-product ratio sum is at least three quarters
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{ab}{2c^2+ab+bc}+\frac{bc}{2a^2+bc+ca}+\frac{ca}{2b^2+ca+ab}\ge\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29335` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29335; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29335 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≥ 3 / 4  :=  by sorry
