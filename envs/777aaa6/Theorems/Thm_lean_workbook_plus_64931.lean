-- Prove2me | Theorems.Thm_lean_workbook_plus_64931
-- name    : lean_workbook_plus_64931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/18871534-e893-480d-a565-2b3d4eb871b3
-- statement:
--   Prove that: a. If $a^2$ = $b^2$ and $a,b \ge 0$ ,then $a=b$ . b.If $a^3$ = $b^3$ and $a,b \ge 0$ ,then $a=b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64931 (a b : ℝ) (h₁ : a ≥ 0 ∧ b ≥ 0 ∧ a^2 = b^2) : a = b   :=  by sorry
