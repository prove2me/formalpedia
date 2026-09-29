-- Prove2me | Theorems.Thm_lean_workbook_plus_19881
-- name    : lean_workbook_plus_19881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/58473682-db08-4692-b82a-f130f2243dfe
-- statement:
--   \(\sqrt{\frac{a+b}{2}} \ge \frac{\sqrt{a} + \sqrt{b}}{2}\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19881 : ∀ a b : ℝ, a ≥ 0 ∧ b ≥ 0 →
  Real.sqrt ((a + b) / 2) ≥ (Real.sqrt a + Real.sqrt b) / 2   :=  by sorry
