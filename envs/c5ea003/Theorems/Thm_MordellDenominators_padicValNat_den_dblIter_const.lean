-- Prove2me | Theorems.Thm_MordellDenominators_padicValNat_den_dblIter_const
-- name    : MordellDenominators.padicValNat_den_dblIter_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:31.514212+00:00
-- url     : https://prove2.me/theorems/6aac7189-be94-4dc3-a7d9-0313441e8ce2
-- title:
--   Constancy along the orbit.
-- statement:
--   **Constancy along the orbit.**  For an odd prime `ℓ` already present in the
--   denominator at step `n`, the `ℓ`-adic valuation of the denominators of the
--   `x`-coordinates is constant from step `n` onwards.
--
--   ```lean
--   theorem MordellDenominators.padicValNat_den_dblIter_const{N : ℤ}
--       (hnt : ∀ x y : ℚ, OnCurve N x y → y ≠ 0) {P : ℚ × ℚ}
--       (h : OnCurve N P.1 P.2) {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) {n : ℕ}
--       (hd : l ∣ (dblIter N n P).1.den) :
--       ∀ m : ℕ, padicValNat l (dblIter N (n + m) P).1.den
--         = padicValNat l (dblIter N n P).1.den := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Valuation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Valuation.lean#L290

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

theorem MordellDenominators.padicValNat_den_dblIter_const{N : ℤ}
    (hnt : ∀ x y : ℚ, OnCurve N x y → y ≠ 0) {P : ℚ × ℚ}
    (h : OnCurve N P.1 P.2) {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) {n : ℕ}
    (hd : l ∣ (dblIter N n P).1.den) :
    ∀ m : ℕ, padicValNat l (dblIter N (n + m) P).1.den
      = padicValNat l (dblIter N n P).1.den := by sorry
