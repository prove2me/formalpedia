-- Prove2me | Theorems.Thm_lean_workbook_plus_52313
-- name    : lean_workbook_plus_52313
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d14be681-b020-4bcd-95f8-d065baefd653
-- statement:
--   Prove that if $ \\sqrt{a_1}+\\sqrt{a_2}+\\cdots + \\sqrt{a^n}$ is rational, and all the $ a_i$ are rational, then each $ a_i$ must be the perfect square of a rational; that is, $ \\sqrt{a_i}$ is rational for each $ a_i$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52313  (n : ℕ)
  (a : ℕ → ℚ)
  (h₁ : ∃ q : ℚ, ∑ i in Finset.range n, Real.sqrt (a i) = q)
  (h₂ : ∀ i, ∃ q : ℚ, a i = q^2) :
  ∀ i, ∃ q : ℚ, Real.sqrt (a i) = q   :=  by sorry
