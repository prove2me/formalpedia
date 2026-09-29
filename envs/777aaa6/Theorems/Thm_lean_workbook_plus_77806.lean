-- Prove2me | Theorems.Thm_lean_workbook_plus_77806
-- name    : lean_workbook_plus_77806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/56af1222-e6b3-4707-9439-2baf4b0a3def
-- statement:
--   If $ q$ is a positive rational number, then we can write $ q=\frac{m}{n}$ for some positive integers with $ \gcd(m,n)=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77806 (q : ℚ) (q_pos : 0 < q) : ∃ m n : ℤ, q = m / n ∧ Int.gcd m n = 1   :=  by sorry
