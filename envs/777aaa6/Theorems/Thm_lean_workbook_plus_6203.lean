-- Prove2me | Theorems.Thm_lean_workbook_plus_6203
-- name    : lean_workbook_plus_6203
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9e3dd0a2-ce89-44f8-a413-a1400cfaf11a
-- statement:
--   Prove that there exist integers $a,b$ (not simultaneously $=0$ ) with $\mid a \mid$ , $\mid b\mid$ $\leq18$ , such that for any real $x,y$ the given inequality stands true: $\mid{ a \sin x + b\cos y } \mid < \frac1 9 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6203 : ∃ a b : ℤ, a ≠ 0 ∨ b ≠ 0 ∧ abs a ≤ 18 ∧ abs b ≤ 18 ∧ ∀ x y : ℝ, abs (a * sin x + b * cos y) < 1 / 9   :=  by sorry
