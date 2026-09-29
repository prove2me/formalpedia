-- Prove2me | Theorems.Thm_lean_workbook_plus_32023
-- name    : lean_workbook_plus_32023
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/45e9ff51-c3a1-465e-b580-f55df563f227
-- statement:
--   Prove that $(-3c^2 + 5c - 3c)^2 - 4(c^2 - 3c + 3)(3c^2 - 3c + 1) \le 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32023 : ∀ c : ℝ, (-3*c^2 + 5*c - 3*c)^2 - 4*(c^2 - 3*c + 3)*(3*c^2 - 3*c + 1) ≤ 0   :=  by sorry
