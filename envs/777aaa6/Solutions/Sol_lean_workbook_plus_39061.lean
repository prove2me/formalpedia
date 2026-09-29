-- Prove2me | solution 1 for lean_workbook_plus_39061
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:23.167956+00:00
-- url     : https://prove2.me/submissions/0a0abe0c-4bb8-466c-925d-142fc7d21529

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℕ → ℕ) (hf : ∀ a b : ℕ, f a + f b = f (a*b)) : f 3 = 5 → f 27 = 15 := by
  intro h3
  have h9 := hf 3 3
  have h27 := hf 3 9
  norm_num at h9 h27
  omega
