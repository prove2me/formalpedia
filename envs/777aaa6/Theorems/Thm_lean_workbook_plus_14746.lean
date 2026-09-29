-- Prove2me | Theorems.Thm_lean_workbook_plus_14746
-- name    : lean_workbook_plus_14746
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/39194e93-ac0e-4949-9047-f01b4cacf8c6
-- statement:
--   $ P(2,2): f(2)^2 = 2f(2)$ . So $ f(2) = 0$ or $ f(2) = 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14746  (f : ℝ → ℝ)
  (h₀ : (∀ x, (f x)^2 = 2 * f x)) :
  f 2 = 0 ∨ f 2 = 2   :=  by sorry
