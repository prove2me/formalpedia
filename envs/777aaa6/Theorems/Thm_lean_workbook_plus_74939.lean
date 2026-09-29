-- Prove2me | Theorems.Thm_lean_workbook_plus_74939
-- name    : lean_workbook_plus_74939
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c9f9e4ce-19f6-421d-a8ad-a58df45c5c5b
-- statement:
--   $\Leftrightarrow$ $\left(s- \frac{3}{2} \right)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74939 : ∀ s : ℝ, s^2 - 3 * s + 9 / 4 ≥ 0 ↔ (s - 3 / 2)^2 ≥ 0   :=  by sorry
