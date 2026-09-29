-- Prove2me | Theorems.Thm_lean_workbook_plus_66261
-- name    : lean_workbook_plus_66261
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e4b738ed-fe7d-4f3f-b39d-0ad09cc10bd3
-- statement:
--   In an acute triangle ABC, we have inequality\n\n$\frac{3}{2}\leq \frac{\cos A}{\cos(B-C)}+\frac{\cos B}{\cos(C-A)} +\frac{\cos C}{\cos(A-B)} <2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66261 :
  ∀ A B C : ℝ, A ∈ Set.Ioo 0 Real.pi ∧ B ∈ Set.Ioo 0 Real.pi ∧ C ∈ Set.Ioo 0 Real.pi ∧ A + B + C = Real.pi →
    3 / 2 ≤ cos A / cos (B - C) + cos B / cos (C - A) + cos C / cos (A - B) ∧
    cos A / cos (B - C) + cos B / cos (C - A) + cos C / cos (A - B) < 2   :=  by sorry
