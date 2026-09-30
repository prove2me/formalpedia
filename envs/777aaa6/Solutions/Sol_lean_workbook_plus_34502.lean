-- Prove2me | solution 1 for lean_workbook_plus_34502
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:37.654102+00:00
-- url     : https://prove2.me/submissions/112787b6-6359-4bb4-bb64-9abcb2eb4c94

import Mathlib
set_option autoImplicit false

theorem solution  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : n.choose 2 ≥ 16) :
  5 ≤ n - 2   := by
  by_contra hnot
  have hn : n ≤ 6 := by omega
  interval_cases n <;> norm_num [Nat.choose] at h₁

#print axioms solution
