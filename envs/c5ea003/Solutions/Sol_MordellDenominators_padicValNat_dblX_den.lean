-- Prove2me | solution 1 for MordellDenominators.padicValNat_dblX_den
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:29:06.144196+00:00
-- url     : https://prove2.me/submissions/26236136-02a2-4b2a-8e82-ba91a67effe5

-- Sol generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_dblX_eq_div
import Theorems.Thm_MordellDenominators_exists_den_param
import Theorems.Thm_MordellDenominators_ne_zero_of_dvd_den
import Theorems.Thm_MordellDenominators_padicValNat_den_of_eq_div

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


/-- The `ℓ`-adic valuation of `x.den` in terms of the parameter `e`. -/
theorem padicValNat_den_eq {x : ℚ} {e : ℕ} (he0 : 0 < e) (hxe : x.den = e ^ 2)
    {l : ℕ} (hl : l.Prime) : padicValNat l x.den = 2 * padicValNat l e := by
  haveI : Fact l.Prime := ⟨hl⟩
  rw [hxe, padicValNat.pow 2 he0.ne']









open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
    (hl : l.Prime) (hd : l ∣ x.den) :
    padicValNat l (dblX N x).den
      = padicValNat l 4 + padicValNat l x.den := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he0, hxe, hye⟩ := exists_den_param h
  have hy : y ≠ 0 := ne_zero_of_dvd_den h hl hd
  have hb0 : y.num ≠ 0 := Rat.num_ne_zero.mpr hy
  have hle : l ∣ e := hl.dvd_of_dvd_pow (by rw [← hxe]; exact hd)
  have hleZ : (l : ℤ) ∣ (e : ℤ) := by exact_mod_cast hle
  have hla : ¬ (l : ℤ) ∣ x.num := by
    intro hcon
    have h1 : l ∣ x.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hcon
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) hd
    exact hl.one_lt.ne' this
  -- `ℓ ∤ y.num`, since `ℓ ∣ e ∣ y.den`
  have hlb : ¬ l ∣ y.num.natAbs := by
    intro hcon
    have hdy : l ∣ y.den := by
      rw [hye]; exact Dvd.dvd.trans hle (dvd_pow_self e (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hcon y.reduced) hdy
    exact hl.one_lt.ne' this
  have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast he0.ne'
  have hBne : (4 * y.num ^ 2 * (e : ℤ) ^ 2 : ℤ) ≠ 0 := by positivity
  have hAdvd : ¬ (l : ℤ) ∣ (x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6) := by
    intro hcon
    have h6 : (l : ℤ) ∣ 8 * N * x.num * (e : ℤ) ^ 6 :=
      Dvd.dvd.mul_left (dvd_pow hleZ (by norm_num)) _
    have hpow : (l : ℤ) ∣ x.num ^ 4 := by
      have := dvd_add hcon h6
      simpa using this
    exact hla ((Nat.prime_iff_prime_int.mp hl).dvd_of_dvd_pow hpow)
  have hden := padicValNat_den_of_eq_div hBne (dblX_eq_div h he0 hxe hye hy) hl hAdvd
  have hnatAbs : (4 * y.num ^ 2 * (e : ℤ) ^ 2 : ℤ).natAbs = 4 * y.num.natAbs ^ 2 * e ^ 2 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  rw [hnatAbs] at hden
  have hbne : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
  have hsplit : padicValNat l (4 * y.num.natAbs ^ 2 * e ^ 2)
      = padicValNat l 4 + 2 * padicValNat l y.num.natAbs + 2 * padicValNat l e := by
    rw [padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by norm_num) (by positivity),
      padicValNat.pow 2 hbne, padicValNat.pow 2 he0.ne']
  rw [hsplit, padicValNat.eq_zero_of_not_dvd hlb] at hden
  rw [hden, padicValNat_den_eq he0 hxe hl]
  omega
