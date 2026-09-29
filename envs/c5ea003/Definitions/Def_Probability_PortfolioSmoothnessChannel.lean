-- Prove2me | Definitions.Def_Probability_PortfolioSmoothnessChannel
-- name    : Probability_PortfolioSmoothnessChannel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:19.967788+00:00
-- url     : https://prove2.me/theorems/9cd25321-43d4-43a5-a3d8-569acbb49b26
-- title:
--   Aether Catalog definitions — Probability_PortfolioSmoothnessChannel
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioSmoothnessChannel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioSmoothnessChannel.lean by skeleton subtraction
import Mathlib
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

namespace Probability.PortfolioRegret

/-! ## The hidden coordinate -/

/-- `n` is `B`-powersmooth: every prime power dividing `n` is at most `B`. -/
def PowerSmooth (B n : ℕ) : Prop := ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ B



/-! ## Two balanced 21-bit semiprimes with opposite hidden coordinate -/





/-- A balanced semiprime instance: both factors are primes of exactly `b + 1`
bits. -/
def BalancedFactorPair (b : ℕ) (x : ℕ × ℕ) : Prop :=
  x.1.Prime ∧ x.2.Prime ∧ 2 ^ b ≤ x.1 ∧ x.1 < 2 ^ (b + 1) ∧ 2 ^ b ≤ x.2 ∧ x.2 < 2 ^ (b + 1)

/-- The hidden coordinate of an instance: both `p - 1` and `q - 1` are
`B`-powersmooth. -/
def SmoothChannel (B : ℕ) (x : ℕ × ℕ) : Prop :=
  PowerSmooth B (x.1 - 1) ∧ PowerSmooth B (x.2 - 1)


/-! ## The paid probe: `p - 1` really does succeed on the smooth class -/

/-- The exponent used by a `p - 1` probe capped at `B`. -/
def lcmUpTo (B : ℕ) : ℕ := (Finset.Icc 1 B).lcm id



end Probability.PortfolioRegret


