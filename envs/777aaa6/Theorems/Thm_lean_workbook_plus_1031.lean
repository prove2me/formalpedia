-- Prove2me | Theorems.Thm_lean_workbook_plus_1031
-- name    : lean_workbook_plus_1031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4b97f9a5-25d9-4be2-8a53-fe492b2438f5
-- statement:
--   Let $x$ be a positive real number. Show that $x + 1 / x \ge 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1031 (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2   :=  by sorry
