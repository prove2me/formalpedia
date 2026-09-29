-- Prove2me | Theorems.Thm_lean_workbook_plus_45372
-- name    : lean_workbook_plus_45372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ae39ad6c-b009-47f6-8d64-c6398c228b34
-- statement:
--   so $ \sqrt{x}=\sqrt{y}$ so $ x=y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45372  (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y)
  (h₁ : Real.sqrt x = Real.sqrt y) :
  x = y   :=  by sorry
