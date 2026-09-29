-- Prove2me | Theorems.Thm_lean_workbook_plus_33041
-- name    : lean_workbook_plus_33041
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4103cc71-d248-4dd9-a033-5809e95ae43f
-- statement:
--   For $1.4<x<1.6$ and $k\in\mathbb{N}, k\ge3$ , holds the equality $\left\lfloor x+\dfrac{1}{k}\right\rfloor=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33041 (x : ℝ) (k : ℕ) (h₁ : 1.4 < x ∧ x < 1.6) (h₂ : 3 ≤ k) : ⌊x + 1 / k⌋ = 1   :=  by sorry
