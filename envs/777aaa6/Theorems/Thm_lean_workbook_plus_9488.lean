-- Prove2me | Theorems.Thm_lean_workbook_plus_9488
-- name    : lean_workbook_plus_9488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/44655249-34a9-4327-b1fd-1025075f1a45
-- statement:
--   Prove that $-\frac{p^2}{6} + \frac{p^3}{2} < 0$ for $0 < p < \frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9488 (p : ℝ) (hp_pos : 0 < p) (hp_lt_on_3 : p < 1/3) : -(p^2 / 6) + p^3 / 2 < 0   :=  by sorry
