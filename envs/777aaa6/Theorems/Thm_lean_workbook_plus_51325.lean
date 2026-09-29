-- Prove2me | Theorems.Thm_lean_workbook_plus_51325
-- name    : lean_workbook_plus_51325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0cfa6b79-8d0d-427d-a2e9-8797af1b3d8d
-- statement:
--   Given the sequence of functions $f_n(x) = \begin{cases} \sqrt{n}, & 0 \leq x \leq \frac{1}{n} \\ 0, & \frac{1}{n} < x \leq 1 \end{cases}$, where $n \geq 1$, show that it does not converge uniformly on $[0, 1]$ using the provided counterexample.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51325 (f : ℕ → ℝ → ℝ) (hf : ∀ n, ∀ x, f n x = if 0 ≤ x ∧ x ≤ 1 / n then Real.sqrt n else 0) : ¬ ∀ ε > 0, ∃ N, ∀ n > N, ∀ x ∈ Set.Icc 0 1, |f n x - 0| < ε   :=  by sorry
