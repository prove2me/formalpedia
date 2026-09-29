-- Prove2me | Theorems.Thm_lean_workbook_plus_36778
-- name    : lean_workbook_plus_36778
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/676efbea-cb5f-4141-94d2-910224122e16
-- statement:
--   Let $N$ be a positive two-digit number with digits $t$ and $d$. The digits are interchanged to form a new number $K$. Prove that $N - K$ is an integral multiple of 9.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36778 (N K : ℕ) (h₁ : 1 ≤ t ∧ t ≤ 9) (h₂ : 0 ≤ d ∧ d ≤ 9) (h₃ : N = 10 * t + d) (h₄ : K = 10 * d + t) : 9 ∣ N - K   :=  by sorry
