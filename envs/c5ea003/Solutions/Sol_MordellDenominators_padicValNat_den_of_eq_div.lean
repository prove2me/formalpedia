-- Prove2me | solution 1 for MordellDenominators.padicValNat_den_of_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:25:28.21677+00:00
-- url     : https://prove2.me/submissions/e43f6f4d-6587-4529-9f93-8064cb673751

-- Sol generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_num_mul_den_eq

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
theorem solution{q : ℚ} {A B : ℤ} (hB : B ≠ 0)
    (hq : q = (A : ℚ) / (B : ℚ)) {l : ℕ} (hl : l.Prime) (hlA : ¬ (l : ℤ) ∣ A) :
    padicValNat l q.den = padicValNat l B.natAbs := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hA : A ≠ 0 := by
    intro h0
    exact hlA (by rw [h0]; exact dvd_zero _)
  have hlAnat : ¬ l ∣ A.natAbs := by
    intro hcon
    exact hlA (Int.ofNat_dvd_left.mpr hcon)
  have hAnat : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA
  have hBnat : B.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact div_ne_zero (Int.cast_ne_zero.mpr hA) (Int.cast_ne_zero.mpr hB)
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0)
  have hden0 : q.den ≠ 0 := q.den_nz
  -- cross multiplication, in `ℕ`
  have key : q.num.natAbs * B.natAbs = A.natAbs * q.den := by
    have hZ : q.num * B = A * (q.den : ℤ) := num_mul_den_eq hB hq
    have := congrArg Int.natAbs hZ
    simpa [Int.natAbs_mul] using this
  have hval : padicValNat l q.num.natAbs + padicValNat l B.natAbs
      = padicValNat l A.natAbs + padicValNat l q.den := by
    have h1 : padicValNat l (q.num.natAbs * B.natAbs)
        = padicValNat l q.num.natAbs + padicValNat l B.natAbs :=
      padicValNat.mul hnum0 hBnat
    have h2 : padicValNat l (A.natAbs * q.den)
        = padicValNat l A.natAbs + padicValNat l q.den :=
      padicValNat.mul hAnat hden0
    rw [← h1, ← h2, key]
  have hvA : padicValNat l A.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hlAnat
  -- the numerator of `q` is prime to `ℓ`
  have hvnum : padicValNat l q.num.natAbs = 0 := by
    by_contra hcon
    have hdvdnum : l ∣ q.num.natAbs := (dvd_iff_padicValNat_ne_zero hnum0).mpr hcon
    have hnotden : ¬ l ∣ q.den := by
      intro hdden
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvdnum q.reduced) hdden
      exact hl.one_lt.ne' this
    have hvden : padicValNat l q.den = 0 := padicValNat.eq_zero_of_not_dvd hnotden
    rw [hvA, hvden] at hval
    omega
  rw [hvnum, hvA] at hval
  omega
