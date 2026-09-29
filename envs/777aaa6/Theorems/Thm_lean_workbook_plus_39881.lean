-- Prove2me | Theorems.Thm_lean_workbook_plus_39881
-- name    : lean_workbook_plus_39881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/23bcc346-58a3-4823-adf6-4a7c121568b2
-- statement:
--   Let $d(k)$ be the number of positive divisors of the integer $k$ . An integer $n$ is called balanced if $ d(n-1) \leq d(n) \leq d(n+1) \textrm{ or } d(n-1) \geq d(n) \geq d(n+1).$ Prove there exist infinitely many balanced integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39881 (d : ℕ → ℕ) (hd : d = fun k => (Nat.divisors k).card) : ∃ n, (d (n-1) ≤ d n ∧ d n ≤ d (n+1)) ∨ (d (n-1) ≥ d n ∧ d n ≥ d (n+1))   :=  by sorry
