-- Prove2me | Theorems.Thm_lean_workbook_plus_38994
-- name    : lean_workbook_plus_38994
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b716e233-613d-4165-b3a8-010bf84e45f2
-- statement:
--   if $ 0 < x < 1$ and $ 0 < y < 1$ and $ y(1 - x) > \frac14$ then $ y > x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38994 (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (h : y * (1 - x) > 1 / 4) : y > x   :=  by sorry
