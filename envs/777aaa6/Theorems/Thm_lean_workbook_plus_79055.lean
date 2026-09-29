-- Prove2me | Theorems.Thm_lean_workbook_plus_79055
-- name    : lean_workbook_plus_79055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6a22e94d-1407-4d63-b515-969d86410613
-- statement:
--   $\sqrt{(x+2)^2+(y+2)^2}\ge \frac{x+2+y+2}{\sqrt{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79055 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2   :=  by sorry
