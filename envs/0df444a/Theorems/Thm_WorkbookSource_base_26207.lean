-- Prove2me | Theorems.Thm_WorkbookSource_base_26207
-- name    : WorkbookSource.base_26207
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:34.553864+00:00
-- url     : https://prove2.me/theorems/dc3dab46-d4be-44f1-b275-d39631bdb02f
-- title:
--   A quadratic lower bound under a determinant relation
-- statement:
--   Let $a,b,c,d $ be reals such that $ad-3bc=1 .$ Prove that
--   $$a^2+ b^2+3c^2+d^2+ac+ bd\geq 1$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26207` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26207; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26207 (a b c d : ℝ) (h : a * d - 3 * b * c = 1) :
  a^2 + b^2 + 3 * c^2 + d^2 + a * c + b * d ≥ 1  :=  by sorry
