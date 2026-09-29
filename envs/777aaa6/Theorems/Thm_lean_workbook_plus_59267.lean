-- Prove2me | Theorems.Thm_lean_workbook_plus_59267
-- name    : lean_workbook_plus_59267
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9df311bc-841e-4272-ae79-b5a6abc3ef0a
-- statement:
--   Let $f: N_+ \rightarrow R_{\ge0}$ be a function such that $f(1) = 1$ and for any positive integer n, $f(n) = \sum_{p\ is\ a\ prime} f(np)$. Prove that for any positive integer n, $f(n^2) \geq f(n)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59267 {f : ℕ → NNReal} (hf1 : f 1 = 1) (hf2 : ∀ n, (0 < n) → f n = ∑ p in Finset.filter (λ p => Nat.Prime p) (Finset.range n), f (n * p)) : ∀ n, (0 < n) → f (n^2) ≥ (f n)^2   :=  by sorry
