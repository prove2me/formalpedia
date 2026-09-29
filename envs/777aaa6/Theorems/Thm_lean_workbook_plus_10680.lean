-- Prove2me | Theorems.Thm_lean_workbook_plus_10680
-- name    : lean_workbook_plus_10680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/68f46443-7d4e-478b-be1e-e62cf0df664f
-- statement:
--   If we have a random variable that follows a binomial distribution \n $X\sim B(n=2m,p=1/2)$ ,\n with mean $E\{ X\}=np=m$ ,\n and variance $\sigma^{2}=E\{(X-E\{ X\})^{2}\}=np(1-p)=m/2$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10680 (m : ℕ) : ∃ n : ℕ, n = 2 * m ∧ ∃ p : ℝ, p = 1 / 2 ∧ ∃ μ : ℝ, μ = n * p ∧ ∃ σ : ℝ, σ ^ 2 = n * p * (1 - p)   :=  by sorry
