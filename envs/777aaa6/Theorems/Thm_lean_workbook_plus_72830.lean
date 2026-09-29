-- Prove2me | Theorems.Thm_lean_workbook_plus_72830
-- name    : lean_workbook_plus_72830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4c93584a-8494-416d-b218-b8fac2b581e5
-- statement:
--   Let $m,n,p,q \in \mathbb{R}$ such that $n \neq 0, q \neq 0$ and $n+q \neq 0$ . Then $\\frac{m}{n} = \\frac{p}{q} = r \Rightarrow \\frac{m+p}{n+q} = r$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72830  (m n p q r : ℝ)
  (h₀ : n ≠ 0 ∧ q ≠ 0 ∧ n + q ≠ 0)
  (h₁ : m / n = r)
  (h₂ : p / q = r) :
  (m + p) / (n + q) = r   :=  by sorry
