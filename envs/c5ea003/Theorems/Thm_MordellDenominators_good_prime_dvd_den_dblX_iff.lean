-- Prove2me | Theorems.Thm_MordellDenominators_good_prime_dvd_den_dblX_iff
-- name    : MordellDenominators.good_prime_dvd_den_dblX_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:29.526219+00:00
-- url     : https://prove2.me/theorems/7970037e-1ce0-4bff-8d3c-77a49eed0a32
-- title:
--   Which good primes enter.
-- statement:
--   **Which good primes enter.**  A prime of good reduction not already in the
--   denominator of `x(P)` divides the denominator of `x(2P)` if and only if it
--   divides the numerator of `y(P)`.  This is the exact form of the counterexample
--   mechanism: the primes that appear are dictated by the point, not by `N`.
--
--   ```lean
--   theorem MordellDenominators.good_prime_dvd_den_dblX_iff{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
--       (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
--       (hnd : ¬ l ∣ x.den) :
--       l ∣ (dblX N x).den ↔ (l : ℤ) ∣ y.num := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Valuation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Valuation.lean#L266

-- Thm stub generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic

/-!
# Exact `ℓ`-adic behaviour of denominators under duplication

`Basic.lean` shows that a prime in a denominator never disappears.  Here we
compute the exact multiplicity, which turns out to be rigid:

* for an **odd** prime `ℓ` in the denominator, duplication *preserves* the
  `ℓ`-adic valuation:
  `padicValNat ℓ (dblX N x).den = padicValNat ℓ x.den`
  (`MordellDenominators.padicValNat_den_dblX_odd`);
* for `ℓ = 2` the valuation increases by exactly `2`
  (`MordellDenominators.padicValNat_den_dblX_two`);
* a good prime `ℓ` *not yet* present enters with the exact valuation
  `2 v_ℓ(num y)` (`MordellDenominators.padicValNat_den_dblX_good`), so it
  enters iff it divides the numerator of the `y`-coordinate
  (`MordellDenominators.good_prime_dvd_den_dblX_iff`).

This is the elementary shadow of the formal-group statement `z(2P) = 2z + …`:
away from the residue characteristic of the multiplier, multiplication by `2`
is an isomorphism of the kernel of reduction, whereas at `ℓ = 2` it strictly
deepens it.  In particular a good prime, once present, occurs with the *same*
exponent forever — the denominators keep broadcasting it.
-/

open MordellDenominators

theorem MordellDenominators.good_prime_dvd_den_dblX_iff{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
    (hnd : ¬ l ∣ x.den) :
    l ∣ (dblX N x).den ↔ (l : ℤ) ∣ y.num := by sorry
