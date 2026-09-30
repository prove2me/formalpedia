-- Prove2me | solution 1 for liouville_transcendental_explicit
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:04:51.078147+00:00
-- url     : https://prove2.me/submissions/e3db97dc-aa57-40cc-b160-d364069a7dc9

import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Localization.Integral

set_option autoImplicit false

theorem solution : Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / 10 ^ n.factorial) := by
  apply mt (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr
  simpa only [liouvilleNumber, Nat.cast_ofNat] using
    (transcendental_liouvilleNumber (m := 10) (by decide))
