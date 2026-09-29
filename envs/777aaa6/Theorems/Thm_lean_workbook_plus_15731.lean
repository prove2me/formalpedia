-- Prove2me | Theorems.Thm_lean_workbook_plus_15731
-- name    : lean_workbook_plus_15731
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a177722c-f8f3-40f0-bf28-92038c0515fd
-- statement:
--   By AM-GM, $\frac{(a + b + c)^3}{3abc} \geq 9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15731 : ∀ a b c : ℝ, (a + b + c) ^ 3 / (3 * a * b * c) ≥ 9   :=  by sorry
