-- Prove2me | solution 1 for Probability.PortfolioRegret.dvd_pow_lcmUpTo_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:47:05.071763+00:00
-- url     : https://prove2.me/submissions/28e12943-46cc-4054-a1e7-ff6f8c8475d6

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




/-! ## Two balanced 21-bit semiprimes with opposite hidden coordinate -/








/-! ## The paid probe: `p - 1` really does succeed on the smooth class -/


/-- A `B`-powersmooth number divides `lcm (1, …, B)`. -/
theorem dvd_lcmUpTo_of_powerSmooth {B n : ℕ} (hs : PowerSmooth B n) :
    n ∣ lcmUpTo B := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hdvd
  have hle : p ^ k ≤ B := hs p k hp hdvd
  have hpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hpos, hle⟩)



open Probability.PortfolioRegret in
theorem solution{B p : ℕ} (hp : p.Prime) (hs : PowerSmooth B (p - 1))
    {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (p : ℤ) ∣ a ^ lcmUpTo B - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := dvd_lcmUpTo_of_powerSmooth hs
  have hazero : ((a : ZMod p)) ≠ 0 := by
    intro h
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hpow : ((a : ZMod p)) ^ lcmUpTo B = 1 := by
    rw [hm, pow_mul, ZMod.pow_card_sub_one_eq_one hazero, one_pow]
  have : ((a ^ lcmUpTo B - 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hpow, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
