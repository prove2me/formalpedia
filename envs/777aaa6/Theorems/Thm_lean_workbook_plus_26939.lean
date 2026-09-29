-- Prove2me | Theorems.Thm_lean_workbook_plus_26939
-- name    : lean_workbook_plus_26939
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/472ea8a8-796e-4cbf-a4dd-ca9ce7818973
-- statement:
--   Let $f(x)$ be a polynomial of degree $n$ with real coefficients and such that $f(x) \ge 0$ for every real number $x$. Show that $f(x) + f'(x) + \dots + f^{(n)}(x) \ge 0$ for all real $x$. $(f^{(k)}(x)$ denotes the $k$th derivative of $f(x))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26939 (n : ℕ) (f : Polynomial ℝ) (hf: ∀ x : ℝ, f.eval x ≥ 0) : ∀ x : ℝ, (∑ k in Finset.range n, (f^k).eval x) ≥ 0   :=  by sorry
