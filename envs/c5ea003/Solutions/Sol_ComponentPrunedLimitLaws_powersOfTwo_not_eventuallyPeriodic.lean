-- Prove2me | solution 1 for ComponentPrunedLimitLaws.powersOfTwo_not_eventuallyPeriodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:44:57.335617+00:00
-- url     : https://prove2.me/submissions/138acd57-7589-4c87-8902-a45bcba74a3d

import Mathlib
import Definitions.Def_Applications_PruningSpectra
open ComponentPrunedLimitLaws in
theorem solution : ¬ EventuallyPeriodic PowersOfTwo := by
  rintro ⟨N, q, hq, h⟩
  -- a power of two beyond both `N` and the period `q`
  have hbig : N + q < 2 ^ (N + q) := Nat.lt_two_pow_self
  obtain ⟨j, hj⟩ := (h (2 ^ (N + q)) (by omega)).mp ⟨N + q, rfl⟩
  -- then `2^(N+q) + q` would be a power of two strictly between `2^(N+q)` and `2^(N+q+1)`
  have h1 : 2 ^ (N + q) < 2 ^ j := by omega
  have h2 : 2 ^ j < 2 ^ (N + q + 1) := by rw [pow_succ]; omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega
