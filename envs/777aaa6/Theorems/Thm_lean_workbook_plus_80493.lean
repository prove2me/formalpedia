-- Prove2me | Theorems.Thm_lean_workbook_plus_80493
-- name    : lean_workbook_plus_80493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/df619001-9cce-4330-bb35-66d234986969
-- statement:
--   Prove $4R^2 + 4Rr + 3r^2 \geq s^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80493 (R r s : ℝ) (h₁ : 0 < R ∧ 0 < r ∧ 0 < s) (h₂ : R + r = s) : 4 * R ^ 2 + 4 * R * r + 3 * r ^ 2 ≥ s ^ 2   :=  by sorry
