-- Prove2me | solution 1 for MordellDenominators.padicValNat_den_dblX_good
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:27:21.100536+00:00
-- url     : https://prove2.me/submissions/255a0584-b8c4-4f26-874d-bff15d273536

-- Sol generated from Cryptography/MordellDenominators/Valuation.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_curve_integral_model
import Theorems.Thm_MordellDenominators_dblX_eq_div
import Theorems.Thm_MordellDenominators_exists_den_param
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











open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hl6N : ¬ ((l : ℤ) ∣ 6 * N))
    (hnd : ¬ l ∣ x.den) :
    padicValNat l (dblX N x).den = 2 * padicValNat l y.num.natAbs := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he0, hxe, hye⟩ := exists_den_param h
  have hb0 : y.num ≠ 0 := Rat.num_ne_zero.mpr hy
  have hbnat : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
  have hle : ¬ l ∣ e := by
    intro hc
    exact hnd (by rw [hxe]; exact hc.trans (dvd_pow_self e (by norm_num)))
  have hleZ : ¬ ((l : ℤ) ∣ (e : ℤ)) := by
    intro hc; exact hle (by exact_mod_cast hc)
  have hlN : ¬ ((l : ℤ) ∣ N) := fun hc => hl6N (Dvd.dvd.mul_left hc 6)
  have hl6 : ¬ ((l : ℤ) ∣ 6) := fun hc => hl6N (Dvd.dvd.mul_right hc N)
  have hl2 : l ≠ 2 := by
    intro hc; exact hl6 (by rw [hc]; norm_num)
  have hl3 : ¬ ((l : ℤ) ∣ 3) := fun hc => hl6 (hc.trans (by norm_num))
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hBne : (4 * y.num ^ 2 * (e : ℤ) ^ 2 : ℤ) ≠ 0 := by
    have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast he0.ne'
    positivity
  have hdiv := dblX_eq_div h he0 hxe hye hy
  have hmodel : y.num ^ 2 = x.num ^ 3 + N * (e : ℤ) ^ 6 := curve_integral_model h hxe hye
  by_cases hlb : (l : ℤ) ∣ y.num
  · -- the prime really enters; compute the valuation of the denominator
    have hlb2 : (l : ℤ) ∣ y.num ^ 2 := Dvd.dvd.trans hlb (dvd_pow_self _ (by norm_num))
    have hla : ¬ ((l : ℤ) ∣ x.num) := by
      intro hc
      have h2 : (l : ℤ) ∣ x.num ^ 3 := Dvd.dvd.trans hc (dvd_pow_self _ (by norm_num))
      have h3 : (l : ℤ) ∣ N * (e : ℤ) ^ 6 := by
        have hsub := dvd_sub hlb2 h2
        rw [hmodel] at hsub
        simpa using hsub
      rcases hlp.dvd_mul.mp h3 with hN | hE
      · exact hlN hN
      · exact hleZ (hlp.dvd_of_dvd_pow hE)
    -- the numerator factors as `a (b² - 9Ne⁶)`, which is prime to `ℓ`
    have hfact : x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6
        = x.num * (y.num ^ 2 - 9 * N * (e : ℤ) ^ 6) := by
      have hx3 : x.num ^ 3 = y.num ^ 2 - N * (e : ℤ) ^ 6 := by linarith [hmodel]
      calc x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6
          = x.num * (x.num ^ 3 - 8 * N * (e : ℤ) ^ 6) := by ring
        _ = x.num * ((y.num ^ 2 - N * (e : ℤ) ^ 6) - 8 * N * (e : ℤ) ^ 6) := by rw [hx3]
        _ = x.num * (y.num ^ 2 - 9 * N * (e : ℤ) ^ 6) := by ring
    have hAne : ¬ ((l : ℤ) ∣ x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6) := by
      rw [hfact]
      intro hc
      rcases hlp.dvd_mul.mp hc with hcx | hcy
      · exact hla hcx
      · have h9 : (l : ℤ) ∣ 9 * N * (e : ℤ) ^ 6 := by
          have := dvd_sub hlb2 hcy
          simpa using this
        rcases hlp.dvd_mul.mp h9 with h9N | hE
        · rcases hlp.dvd_mul.mp h9N with h9' | hN
          · refine hl3 (hlp.dvd_of_dvd_pow (n := 2) ?_)
            rw [show ((3 : ℤ) ^ 2) = 9 by norm_num]
            exact h9'
          · exact hlN hN
        · exact hleZ (hlp.dvd_of_dvd_pow hE)
    have hval := padicValNat_den_of_eq_div hBne hdiv hl hAne
    have hnatAbs : (4 * y.num ^ 2 * (e : ℤ) ^ 2 : ℤ).natAbs
        = 4 * y.num.natAbs ^ 2 * e ^ 2 := by
      simp [Int.natAbs_mul, Int.natAbs_pow]
    rw [hnatAbs] at hval
    have hsplit : padicValNat l (4 * y.num.natAbs ^ 2 * e ^ 2)
        = padicValNat l 4 + 2 * padicValNat l y.num.natAbs + 2 * padicValNat l e := by
      rw [padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (by norm_num) (by positivity),
        padicValNat.pow 2 hbnat, padicValNat.pow 2 he0.ne']
    have h4 : padicValNat l 4 = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hc
      have : l ∣ 2 ^ 2 := by simpa using hc
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow this))
    have hve : padicValNat l e = 0 := padicValNat.eq_zero_of_not_dvd hle
    rw [hval, hsplit, h4, hve]
    omega
  · -- the prime is absent from the numerator of `y`: both sides vanish
    have hvb : padicValNat l y.num.natAbs = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hc
      exact hlb (Int.ofNat_dvd_left.mpr hc)
    have hdenDvd : ((dblX N x).den : ℤ) ∣ (4 * y.num ^ 2 * (e : ℤ) ^ 2) := by
      have := Rat.den_dvd (x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6)
        (4 * y.num ^ 2 * (e : ℤ) ^ 2)
      rwa [← Rat.intCast_div_eq_divInt, ← hdiv] at this
    have hnotdvd : ¬ l ∣ (dblX N x).den := by
      intro hc
      have hcZ : (l : ℤ) ∣ ((dblX N x).den : ℤ) := Int.ofNat_dvd_left.mpr hc
      have hB : (l : ℤ) ∣ 4 * y.num ^ 2 * (e : ℤ) ^ 2 := hcZ.trans hdenDvd
      rcases hlp.dvd_mul.mp hB with h1 | h2
      · rcases hlp.dvd_mul.mp h1 with h3 | h4
        · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
            (hl.dvd_of_dvd_pow (n := 2) (by
              have : (l : ℤ) ∣ (4 : ℤ) := h3
              have : l ∣ 4 := by exact_mod_cast this
              simpa using this)))
        · exact hlb (hlp.dvd_of_dvd_pow h4)
      · exact hleZ (hlp.dvd_of_dvd_pow h2)
    rw [padicValNat.eq_zero_of_not_dvd hnotdvd, hvb]
