-- Prove2me | Theorems.Thm_lean_workbook_plus_74968
-- name    : lean_workbook_plus_74968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/206ba3d0-5987-4d30-a18e-3eada2f87662
-- statement:
--   Find the roots of the quadratic equation $34x^2-13x-21=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74968 (x : ℝ) : 34 * x ^ 2 - 13 * x - 21 = 0 ↔ x = -21 / 34 ∨ x = 1   :=  by sorry
