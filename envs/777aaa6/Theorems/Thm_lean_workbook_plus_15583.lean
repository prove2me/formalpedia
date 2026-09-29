-- Prove2me | Theorems.Thm_lean_workbook_plus_15583
-- name    : lean_workbook_plus_15583
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2ea18446-7d2e-40a8-bf1e-71117916007b
-- statement:
--   Prove that $\sin(\alpha)^2+\sin(\beta)^2+1 \geq \sin(\alpha)+\sin(\beta)+\sin(\alpha)\sin(\beta)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15583 (α β : ℝ) : (sin α)^2 + (sin β)^2 + 1 ≥ sin α + sin β + sin α * sin β   :=  by sorry
