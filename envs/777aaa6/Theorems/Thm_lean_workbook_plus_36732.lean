-- Prove2me | Theorems.Thm_lean_workbook_plus_36732
-- name    : lean_workbook_plus_36732
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7a434360-68ff-4776-8a32-fc0429424aa0
-- statement:
--   Let $n$ equal the amount of gillyweed in the first cauldron. Our equation is: $n+n+1+n+1...+n+6=3(n+6)+3$ Expanding the left side gives us: $n+n+1+n+2...+n+6=3n+21$ Our equation is now: $7n+21=3n+21$ This means that: $4n=0$ Therefore, the amount of gillyweed in the first cauldron is $n=\boxed{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36732  (n : ℕ)
  (h₀ : ∑ k in Finset.Icc 0 6, (n + k) = 3 * (n + 6) + 3) :
  n = 0   :=  by sorry
