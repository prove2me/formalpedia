-- Prove2me | Theorems.Thm_lean_workbook_plus_51858
-- name    : lean_workbook_plus_51858
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4036e15b-24d0-49f3-b676-0c41b724a063
-- statement:
--   Prove the inequality \(3t^2(4+20t+31t^2+25t^3)\geq 0\) for \(0\leq t<1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51858 : ∀ t : ℝ, 0 ≤ t ∧ t < 1 → 3 * t^2 * (4 + 20 * t + 31 * t^2 + 25 * t^3) ≥ 0   :=  by sorry
