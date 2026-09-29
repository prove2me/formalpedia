-- Prove2me | Theorems.Thm_lean_workbook_plus_10990
-- name    : lean_workbook_plus_10990
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5bf92795-7378-4f11-8e95-f10288717e79
-- statement:
--   Prove that \((1 + 1)^n = \binom{n}{0}1^n + \binom{n}{1}1^{n - 1}*1 + ... + \binom{n}{n - 1}1* 1^{n - 1} + \binom{n}{n}1^n = \binom{n}{0} + \binom{n}{1} + ... + \binom{n}{n - 1} + \binom{n}{n}\) using the Binomial theorem
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10990 (n : ℕ) : (1 + 1)^n = ∑ k in Finset.range n, (Nat.choose n k * 1 ^ k * 1 ^ (n - k))   :=  by sorry
