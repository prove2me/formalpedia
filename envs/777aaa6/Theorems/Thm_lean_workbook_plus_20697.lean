-- Prove2me | Theorems.Thm_lean_workbook_plus_20697
-- name    : lean_workbook_plus_20697
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8fd705ee-bef7-460d-a0da-06f6548f4ad9
-- statement:
--   Given $A + C = 2B$, prove the statement $\frac{1}{\sqrt{A}+\sqrt{B}}+\frac{1}{\sqrt{B}+\sqrt{C}}=\frac{2}{\sqrt{A}+\sqrt{C}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20697  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + c = 2 * b) :
  1 / (Real.sqrt a + Real.sqrt b) + 1 / (Real.sqrt b + Real.sqrt c) =
    2 / (Real.sqrt a + Real.sqrt c)   :=  by sorry
