-- Prove2me | Theorems.Thm_lean_workbook_plus_8055
-- name    : lean_workbook_plus_8055
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7a89f96e-8642-466e-b8f6-09103cebd422
-- statement:
--   Find the ordered pair (A,B) where A and B are radian measure of acute angles such that \(\frac{\sin(A)}{\sin(B)}=3\) and \(\frac{\tan(A)}{\tan(B)}=3\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8055 (A B : ℝ) (hA : 0 < A ∧ A <= π/2) (hB : 0 < B ∧ B <= π/2) (hA0 : sin A / sin B = 3) (hA1 : tan A / tan B = 3) : A = π/3 ∧ B = π/6   :=  by sorry
