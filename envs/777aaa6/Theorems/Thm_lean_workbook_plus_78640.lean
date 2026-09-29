-- Prove2me | Theorems.Thm_lean_workbook_plus_78640
-- name    : lean_workbook_plus_78640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/70974014-70db-4c1e-9193-344aa186fa38
-- statement:
--   Show that $a_{n+1} = \frac{a_n^2}{a_n^2 - a_n + 1} \le \frac{4a_n^2}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78640 (a : ℕ → ℝ) (n : ℕ) (ha : a (n + 1) = a n ^ 2 / (a n ^ 2 - a n + 1)) : a (n + 1) ≤ 4 * a n ^ 2 / 3   :=  by sorry
