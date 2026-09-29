-- Prove2me | solution 1 for MordellDenominators.good_prime_dvd_den_dblX_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:29:04.439435+00:00
-- url     : https://prove2.me/submissions/cb9ef615-7edb-4dce-9abc-528824f2e768

-- Sol generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_padicValNat_den_dblX_good

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











open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
    (hnd : ¬ l ∣ x.den) :
    l ∣ (dblX N x).den ↔ (l : ℤ) ∣ y.num := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hb0 : y.num ≠ 0 := Rat.num_ne_zero.mpr hy
  have hbnat : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
  have hval := padicValNat_den_dblX_good h hy hl hl6N hnd
  have hden0 : (dblX N x).den ≠ 0 := (dblX N x).den_nz
  constructor
  · intro hc
    have h1 : padicValNat l (dblX N x).den ≠ 0 := (dvd_iff_padicValNat_ne_zero hden0).mp hc
    have h2 : padicValNat l y.num.natAbs ≠ 0 := by omega
    exact Int.ofNat_dvd_left.mpr ((dvd_iff_padicValNat_ne_zero hbnat).mpr h2)
  · intro hc
    have hcn : l ∣ y.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hc
    have h2 : padicValNat l y.num.natAbs ≠ 0 := (dvd_iff_padicValNat_ne_zero hbnat).mp hcn
    have h1 : padicValNat l (dblX N x).den ≠ 0 := by omega
    exact (dvd_iff_padicValNat_ne_zero hden0).mpr h1
