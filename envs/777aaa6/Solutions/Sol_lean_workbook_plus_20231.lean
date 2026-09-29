-- Prove2me | solution 1 for lean_workbook_plus_20231
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:28.345729+00:00
-- url     : https://prove2.me/submissions/89c431d2-3a51-41fc-bd55-f83611969b12

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p : ℕ) (hp : p.Prime) (h : p ≡ 0 [ZMOD 3]) : p = 3 := by
  have hd := Int.modEq_zero_iff_dvd.mp h
  have hd' : 3 ∣ p := by exact_mod_cast hd
  rcases (Nat.dvd_prime hp).mp hd' with h1 | h2
  · norm_num at h1
  · exact h2.symm
