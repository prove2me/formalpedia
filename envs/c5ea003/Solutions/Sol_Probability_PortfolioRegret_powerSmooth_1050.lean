-- Prove2me | solution 1 for Probability.PortfolioRegret.powerSmooth_1050
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:37.880958+00:00
-- url     : https://prove2.me/submissions/bb1f7860-3cd5-4560-b788-b18f68db97a2

-- Sol generated from Probability/PortfolioSmoothnessChannel.lean
import Mathlib
import Definitions.Def_Probability_PortfolioSmoothnessChannel
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The hidden channel is number-theoretic: `p - 1` powersmoothness

The abstract model of `Probability.PortfolioRegretCore` assumes an *invisible*
organising channel: a hidden coordinate that decides which member of a factoring
portfolio wins, and which the observable features of the modulus `N` do not
resolve.  This file supplies the number theory behind that assumption.

* `PowerSmooth` — the hidden coordinate: `B`-powersmoothness of `p - 1`.
* `Probability.PortfolioRegret.smoothness_invisible_at_bitlength_11` — an
  explicit witness that the observable `(bit length of N, bit lengths of the two
  factors)` does *not* determine the hidden coordinate: two balanced semiprimes
  of exactly `21` bits, with both factors of exactly `11` bits, one of which has
  both `p - 1` and `q - 1` `256`-powersmooth while the other has neither.
  Hence the observation fiber genuinely contains both smoothness classes: the
  channel is `N`-invisible in the strong, pointwise sense.
* `Probability.PortfolioRegret.dvd_pow_lcmUpTo_sub_one` — the *paid probe* pays
  off: if `p - 1` is `B`-powersmooth then `p` divides `a ^ L - 1` for
  `L = lcm(1, …, B)` and any `a` prime to `p`.  This is exactly the guarantee
  behind a short-capped `p - 1` probe, so the value-of-information theorems of
  the core file are not vacuous.
-/

open Probability.PortfolioRegret

/-! ## The hidden coordinate -/


/-- Bounding a prime power divisor by exhibiting a higher power that fails to
divide. -/
theorem pow_le_of_pow_not_dvd {p k m n B : ℕ} (hp : 1 < p) (hdvd : p ^ k ∣ n)
    (hnd : ¬ p ^ m ∣ n) (hB : p ^ (m - 1) ≤ B) : p ^ k ≤ B := by
  have hk : k < m := by
    by_contra h
    exact hnd (dvd_trans (pow_dvd_pow p (not_lt.mp h)) hdvd)
  exact le_trans (Nat.pow_le_pow_right (le_of_lt hp) (by omega)) hB


/-! ## Two balanced 21-bit semiprimes with opposite hidden coordinate -/








/-! ## The paid probe: `p - 1` really does succeed on the smooth class -/





open Probability.PortfolioRegret in
theorem solution: PowerSmooth 256 1050 := by
  intro p k hp hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  have hpd : p ∣ 1050 := dvd_trans (dvd_pow_self p hk.ne') hdvd
  rw [show (1050 : ℕ) = 2 * (3 * (5 ^ 2 * 7)) by norm_num] at hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    subst hp2
    exact pow_le_of_pow_not_dvd (m := 2) (by norm_num) hdvd (by norm_num) (by norm_num)
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    subst hp3
    exact pow_le_of_pow_not_dvd (m := 2) (by norm_num) hdvd (by norm_num) (by norm_num)
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)
    subst hp5
    exact pow_le_of_pow_not_dvd (m := 3) (by norm_num) hdvd (by norm_num) (by norm_num)
  · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    subst hp7
    exact pow_le_of_pow_not_dvd (m := 2) (by norm_num) hdvd (by norm_num) (by norm_num)
