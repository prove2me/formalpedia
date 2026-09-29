-- Prove2me | Theorems.Thm_lean_workbook_plus_39801
-- name    : lean_workbook_plus_39801
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/dd247555-1b94-4806-8587-dc31b5fac7bc
-- statement:
--   Let $ \Delta ABC$ be a acute triangle, prove that:\n$ \frac {cos A. cos B}{sin2C} + \frac {cos B . cos C}{sin2A} + \frac { cos C . cos A}{sin2B}\ge \frac {\sqrt {3}}{2}$\n\nThe inequality can be written in the algebraic form:\n\nIf $ a,$ $ b,$ $ c$ are positive real numbers, then\n$ \frac{\sqrt{a(a+b)(a+c)}}{b+c}+\frac{\sqrt{b(b+c)(b+a)}}{c+a}+\frac{\sqrt{c(c+a) (c+b)}}{a+b} \ge \sqrt{3(a+b+c)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39801 :
  ∀ ⦃A B C : ℝ⦄, A ∈ Set.Ioo 0 Real.pi ∧ B ∈ Set.Ioo 0 Real.pi ∧ C ∈ Set.Ioo 0 Real.pi ∧ A + B + C = Real.pi →
    Real.cos A * Real.cos B / Real.sin (2 * C) + Real.cos B * Real.cos C / Real.sin (2 * A) +
        Real.cos C * Real.cos A / Real.sin (2 * B) ≥ Real.sqrt 3 / 2   :=  by sorry
