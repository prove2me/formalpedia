-- Prove2me | Theorems.Thm_lean_workbook_plus_5846
-- name    : lean_workbook_plus_5846
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/bae4bf95-a44d-49b4-bdf7-0cd4cc80d256
-- statement:
--   Assume all $ 0\le A,B,C<\frac{\pi}{2}$ . Then $ 0 < \cos{A},\cos{B},\cos{C}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5846 (A B C : ℝ) (hA : 0 < A ∧ A < Real.pi / 2) (hB : 0 < B ∧ B < Real.pi / 2) (hC : 0 < C ∧ C < Real.pi / 2) : 0 < Real.cos A ∧ Real.cos A <= 1 ∧ 0 < Real.cos B ∧ Real.cos B <= 1 ∧ 0 < Real.cos C ∧ Real.cos C <= 1   :=  by sorry
