-- Prove2me | Theorems.Thm_lean_workbook_plus_15833
-- name    : lean_workbook_plus_15833
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c3bc76f0-38c3-4177-b1f2-add999fb9b73
-- statement:
--   Find the values of $x \in \mathbb{C}$ that satisfy $f^{(n)}(x) = \pm i$ for some nonnegative integer $n$, where $f^{(n)}(x)$ denotes the $n$-th iterate of $f(x) = x^2 + x + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15833 (x : ℂ) (n : ℕ) : (∃ k : ℕ, (f^[k] x = i ∨ f^[k] x = -i)) ↔ ∃ k : ℕ, (f^[k] x = i ∨ f^[k] x = -i)   :=  by sorry
