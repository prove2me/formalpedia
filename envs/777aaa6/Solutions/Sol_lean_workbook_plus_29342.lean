-- Prove2me | solution 1 for lean_workbook_plus_29342
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:56.485348+00:00
-- url     : https://prove2.me/submissions/c5b24a3d-7901-4244-bcf1-3bfdd73b061c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n r : ℕ)
  (h₀ : 0 < n ∧ 0 < r)
  (h₁ : r ≤ n) :
  Nat.choose n r = Nat.choose (n - 1) (r - 1) + Nat.choose (n - 1) r := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  simpa using Nat.choose_succ_succ n r
