-- Prove2me | solution 1 for lean_workbook_plus_3649
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:22:47.345079+00:00
-- url     : https://prove2.me/submissions/e452b41e-04ba-4186-85d7-d7324b9573fc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Real.Sqrt
set_option autoImplicit false
theorem solution (x y : ℕ) (hx: 4^x ≡ 1 [ZMOD 9]) (hy: 2^y ≡ 0 [ZMOD 7]) : x = 3 ∧ y = 3 := by
  have hp : Prime (7 : ℤ) := by exact Int.prime_iff_natAbs_prime.mpr (by decide)
  have hd : (7 : ℤ) ∣ 2 ^ y := Int.modEq_zero_iff_dvd.mp hy
  have hf := hp.dvd_of_dvd_pow hd
  norm_num at hf
