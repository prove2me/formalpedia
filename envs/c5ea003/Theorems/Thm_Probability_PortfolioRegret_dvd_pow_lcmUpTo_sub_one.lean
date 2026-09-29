-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_dvd_pow_lcmUpTo_sub_one
-- name    : Probability.PortfolioRegret.dvd_pow_lcmUpTo_sub_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:49.232542+00:00
-- url     : https://prove2.me/theorems/3f22c98c-4bbf-46a4-8ec3-cde6aa4801e2
-- title:
--   The probe pays off.
-- statement:
--   **The probe pays off.**  If the hidden coordinate of the prime factor `p` is
--   `B`-smooth, then a `p - 1` probe capped at `B` exposes `p`: for every `a` not
--   divisible by `p`, `p ∣ a ^ lcm(1, …, B) - 1`, so `gcd (a ^ L - 1, N)` is a
--   nontrivial factor of any `N` that `p` divides.
--
--   ```lean
--   theorem Probability.PortfolioRegret.dvd_pow_lcmUpTo_sub_one{B p : ℕ} (hp : p.Prime) (hs : PowerSmooth B (p - 1))
--       {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (p : ℤ) ∣ a ^ lcmUpTo B - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioSmoothnessChannel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioSmoothnessChannel.lean#L145

-- Thm stub generated from Probability/PortfolioSmoothnessChannel.lean
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

theorem Probability.PortfolioRegret.dvd_pow_lcmUpTo_sub_one{B p : ℕ} (hp : p.Prime) (hs : PowerSmooth B (p - 1))
    {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (p : ℤ) ∣ a ^ lcmUpTo B - 1 := by sorry
