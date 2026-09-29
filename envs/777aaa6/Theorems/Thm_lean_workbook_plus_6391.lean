-- Prove2me | Theorems.Thm_lean_workbook_plus_6391
-- name    : lean_workbook_plus_6391
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f8d5bc8a-ff95-4679-b5b1-26c87526ab52
-- statement:
--   Suppose for any $\theta \in \mathbb{R}$ , the modulus of $z = (a+\cos \theta)+(2a-\sin \theta)i$ never exceeds 2, then the range of $a \in \mathbb{R}$ is
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6391 (a : ℝ) (z : ℂ) (h : ∀ θ : ℝ, ‖(a + Real.cos θ) + (2 * a - Real.sin θ) * Complex.I‖ ≤ 2) : -2 ≤ a ∧ a ≤ 2   :=  by sorry
