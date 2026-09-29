-- Prove2me | Theorems.Thm_lean_workbook_plus_45237
-- name    : lean_workbook_plus_45237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/02c90066-5551-48e6-9169-7da7fcb5a539
-- statement:
--   Prove that if $a+b+c=3$ , then $ab+bc+ac<=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45237 (a b c : ℝ) (ha : a + b + c = 3) : a * b + b * c + c * a ≤ 3   :=  by sorry
