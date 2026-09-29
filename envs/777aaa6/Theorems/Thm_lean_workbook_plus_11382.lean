-- Prove2me | Theorems.Thm_lean_workbook_plus_11382
-- name    : lean_workbook_plus_11382
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/786c2c62-e7a8-4272-8b6d-33d6e96b554a
-- statement:
--   Prove that $\sqrt{\frac{x^2 +y^2}{2}} \geq \frac{x+y}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11382 (x y : ℝ) : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ (x + y) / 2   :=  by sorry
