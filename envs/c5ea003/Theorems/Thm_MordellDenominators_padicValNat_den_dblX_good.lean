-- Prove2me | Theorems.Thm_MordellDenominators_padicValNat_den_dblX_good
-- name    : MordellDenominators.padicValNat_den_dblX_good
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:30.010068+00:00
-- url     : https://prove2.me/theorems/f2615597-8ee9-40a1-b46e-7b0284603c6b
-- title:
--   Entry of a good prime, exactly.
-- statement:
--   **Entry of a good prime, exactly.**  Let `ℓ` be a prime of good reduction
--   (`ℓ ∤ 6N`) that is *not yet* in the denominator of `x(P)`.  Then the `ℓ`-adic
--   valuation of the denominator of `x(2P)` is exactly twice the `ℓ`-adic valuation
--   of the numerator of `y(P)`:
--   `v_ℓ(den x(2P)) = 2 v_ℓ(num y)`.
--
--   In particular a good prime enters the orbit precisely when it divides the
--   numerator of the `y`-coordinate, and it enters with the minimal exponent `2`
--   exactly when it divides that numerator exactly once.
--
--   ```lean
--   theorem MordellDenominators.padicValNat_den_dblX_good{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
--       (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
--       (hnd : ¬ l ∣ x.den) :
--       padicValNat l (dblX N x).den = 2 * padicValNat l y.num.natAbs := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Valuation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Valuation.lean#L155

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

theorem MordellDenominators.padicValNat_den_dblX_good{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
    (hnd : ¬ l ∣ x.den) :
    padicValNat l (dblX N x).den = 2 * padicValNat l y.num.natAbs := by sorry
