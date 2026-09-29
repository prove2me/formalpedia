-- Prove2me | Theorems.Thm_lean_workbook_plus_29924
-- name    : lean_workbook_plus_29924
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f9605938-54c7-4293-b77e-c02ac6a1770e
-- statement:
--   Prove that $\sum_{d|n} \phi (d) =n$ where $\phi$ is the Euler's totient function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29924 (n : ℕ) : ∑ d in n.divisors, φ d = n   :=  by sorry
