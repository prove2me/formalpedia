-- Prove2me | Theorems.Thm_MordellDenominators_padicValNat_den_of_eq_div
-- name    : MordellDenominators.padicValNat_den_of_eq_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:10.119209+00:00
-- url     : https://prove2.me/theorems/cf375b17-f543-44c8-9482-533c224e800e
-- title:
--   Valuation of a denominator.
-- statement:
--   **Valuation of a denominator.**  If `q = A/B` with `ℓ ∤ A`, then the
--   `ℓ`-adic valuation of the reduced denominator of `q` is that of `B`.
--
--   ```lean
--   theorem MordellDenominators.padicValNat_den_of_eq_div{q : ℚ} {A B : ℤ} (hB : B ≠ 0)
--       (hq : q = (A : ℚ) / (B : ℚ)) {l : ℕ} (hl : l.Prime) (hlA : ¬ (l : ℤ) ∣ A) :
--       padicValNat l q.den = padicValNat l B.natAbs := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Valuation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Valuation.lean#L28

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

theorem MordellDenominators.padicValNat_den_of_eq_div{q : ℚ} {A B : ℤ} (hB : B ≠ 0)
    (hq : q = (A : ℚ) / (B : ℚ)) {l : ℕ} (hl : l.Prime) (hlA : ¬ (l : ℤ) ∣ A) :
    padicValNat l q.den = padicValNat l B.natAbs := by sorry
