-- Prove2me | solution 1 for lean_workbook_plus_33307
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:18:15.731285+00:00
-- url     : https://prove2.me/submissions/3b3fa545-3e53-4801-aa6a-a8d640da89f2

import Mathlib

set_option autoImplicit false

theorem corrected_residue (t : Nat) (ht : t % 6 = 0) :
    (1^t + 2^t + 4^t + 5^t + 7^t + 8^t) % 9 = 6 := by
  have he : t = 6*(t/6) := by omega
  have hp (a : Nat) (ha : a^6 ≡ 1 [MOD 9]) : a^t ≡ 1 [MOD 9] := by
    rw [he, pow_mul]
    simpa using ha.pow (t/6)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  exact (((((h1.add h2).add h4).add h5).add h7).add h8)

theorem solution : ¬ (∀ t : Nat, t % 6 = 0 →
    (1^t + 2^t + 4^t + 5^t + 7^t + 8^t) % 9 = 0) := by
  intro h
  have hbad := h 6 (by decide)
  rw [corrected_residue 6 (by decide)] at hbad
  contradiction

#print axioms solution
