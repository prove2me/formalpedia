-- Prove2me | Theorems.Thm_lean_workbook_plus_30442
-- name    : lean_workbook_plus_30442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/483b44e7-d628-4b2a-a67e-43ec7bd3019e
-- statement:
--   Prove or disprove: Given $\alpha$ , an irrational real number, the set $\{ k\alpha - \lfloor k\alpha \rfloor : k \in \mathbb{N}\}$ is dense in $[0,1]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30442 (α : ℝ) (h : ¬ ∃ a : ℚ, α = a) :
  ∀ ε : ℝ, ε > 0 → ∃ k : ℕ, |k * α - ⌊k * α⌋| < ε   :=  by sorry
