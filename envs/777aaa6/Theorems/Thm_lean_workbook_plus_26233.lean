-- Prove2me | Theorems.Thm_lean_workbook_plus_26233
-- name    : lean_workbook_plus_26233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4ac028fe-7d23-4ec4-bfe8-330c986a0c41
-- statement:
--   Prove that for all $t \in [0, 1)$, the inequality $\frac{3(1 + t)(1 - 2t)^2 t^2}{(1 + 2t)(1 - t)} \ge 0$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26233 (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : (3 * (1 + t) * (1 - 2 * t) ^ 2 * t ^ 2) / (1 + 2 * t) / (1 - t) ≥ 0   :=  by sorry
