-- Prove2me | solution 1 for lean_workbook_plus_43592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:22.218571+00:00
-- url     : https://prove2.me/submissions/e9f600ff-7289-44d1-a88c-35e552e02cc5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n ≥ 2, (2^n - 1) % 4 = 3 := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hp : 0 < (2 : ℕ)^k := by positivity
  norm_num [pow_add]
  omega
