-- Prove2me | Theorems.Thm_lean_workbook_plus_29847
-- name    : lean_workbook_plus_29847
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c714a6ef-ddef-4236-9fb3-36160c5ae3e1
-- statement:
--   Let $n\in\mathbb{N},n\geq4 $. Prove that: $\frac{2^n}{n}\leq\frac{C_n^0}{1}+\frac{C_n^1}{3}+...+\frac{C_n^n}{2n+1}\leq\frac{2^n}{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29847 : ∀ n ≥ 4, (2 : ℝ)^n / n ≤ ∑ i in Finset.range (n + 1), (n.choose i) / (2 * i + 1) ∧ ∑ i in Finset.range (n + 1), (n.choose i) / (2 * i + 1) ≤ (2 : ℝ)^n / (n - 1)   :=  by sorry
