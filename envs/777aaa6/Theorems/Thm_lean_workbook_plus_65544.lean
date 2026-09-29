-- Prove2me | Theorems.Thm_lean_workbook_plus_65544
-- name    : lean_workbook_plus_65544
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/96fe368a-4a82-4af1-963c-7bae22bf340d
-- statement:
--   Given $ a, b, c > 0$ . Prove that: $ \frac {2 + x}{2 + y}\ge \frac {x + y + xy}{x + y + y^2}$ $ (x,y>0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65544 ∀ x y : ℝ, x > 0 ∧ y > 0 → (2 + x) / (2 + y) ≥ (x + y + x * y) / (x + y + y ^ 2)   :=  by sorry
