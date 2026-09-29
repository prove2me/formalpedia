-- Prove2me | Theorems.Thm_lean_workbook_plus_42612
-- name    : lean_workbook_plus_42612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/af69d822-3962-4af1-b0f8-4f6048615ac7
-- statement:
--   Case 1: \(n=m\) \nOur expression equals \(\frac{\gcd{(n,n)}}{n}\binom{n}{n}=1\) , which is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42612  (n : ℕ)
  (h₀ : 0 < n) :
  ((Nat.gcd n n) / n * (n.choose n) : ℚ).den = 1   :=  by sorry
