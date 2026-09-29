-- Prove2me | solution 1 for MordellDenominators.dblX_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:23.112002+00:00
-- url     : https://prove2.me/submissions/5fb27431-018f-4c7c-9fd4-0f2a8cbe6d84

-- Sol generated from Cryptography/MordellDenominators/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic

/-!
# Denominators of rational points on Mordell curves `E_N : y² = x³ + N`

This file develops the *denominator theory* of rational points on the Mordell
curve `E_N : y² = x³ + N` (`N : ℤ`), the arithmetic object behind the folklore
conjecture that denominators of multiples of a rational point only involve the
primes of bad reduction `{2, 3} ∪ {p : p ∣ N}`.

Main results.

* `MordellDenominators.den_sq_eq_den_cube` : for any rational point,
  `y.den ^ 2 = x.den ^ 3`.
* `MordellDenominators.exists_den_param` : consequently there is `e ≥ 1` with
  `x.den = e ^ 2` and `y.den = e ^ 3` (the classical `(e², e³)` shape).
* `MordellDenominators.prime_dvd_x_den_iff_dvd_y_den`, `sq_dvd_x_den`,
  `cube_dvd_y_den` : a prime dividing one denominator divides both, to order
  `≥ 2` resp. `≥ 3`; i.e. the point lies in the kernel of reduction there.
* `MordellDenominators.dbl_onCurve` : the duplication formula lands on the
  curve again.
* `MordellDenominators.dvd_den_dblX_of_dvd_den` : the kernel of reduction at
  any prime `ℓ` is stable under duplication — once a prime enters a
  denominator it stays for the whole doubling orbit.

Everything is elementary (no `EllipticCurve` API is needed) and explicit, so
that the counterexamples in `Counterexample.lean` and the infinite family in
`Family.lean` can be checked against these general theorems.
-/

open MordellDenominators

/-! ## Basic definitions -/










/-! ## A divisibility criterion for denominators -/



/-! ## The `(e², e³)` shape of denominators -/







/-! ## The duplication formula -/


/-! ## Stability of the kernel of reduction under duplication -/




/-! ## Orbits under duplication -/






open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {e : ℕ} (he0 : 0 < e)
    (hxe : x.den = e ^ 2) (hye : y.den = e ^ 3) (hy : y ≠ 0) :
    dblX N x = ((x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6 : ℤ) : ℚ) /
      (((4 * y.num ^ 2 * (e : ℤ) ^ 2 : ℤ)) : ℚ) := by
  set a : ℤ := x.num with ha
  set b : ℤ := y.num with hb
  have hex : (e : ℚ) ≠ 0 := by exact_mod_cast he0.ne'
  have hxeq : x = (a : ℚ) / ((e : ℚ) ^ 2) := by
    have h2 : ((e : ℚ) ^ 2) = (x.den : ℚ) := by rw [hxe]; push_cast; ring
    rw [h2, ha, Rat.num_div_den]
  have hyeq : y = (b : ℚ) / ((e : ℚ) ^ 3) := by
    have h3 : ((e : ℚ) ^ 3) = (y.den : ℚ) := by rw [hye]; push_cast; ring
    rw [h3, hb, Rat.num_div_den]
  have hx3 : x ^ 3 + (N : ℚ) = y ^ 2 := h.symm
  have hb0 : b ≠ 0 := by
    intro h0
    exact hy (by rw [hyeq, h0]; simp)
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hnum : x ^ 4 - 8 * (N : ℚ) * x =
      ((a ^ 4 - 8 * N * a * (e : ℤ) ^ 6 : ℤ) : ℚ) / ((e : ℚ) ^ 8) := by
    rw [hxeq]; push_cast; field_simp
  have hden : 4 * (x ^ 3 + (N : ℚ)) = ((4 * b ^ 2 : ℤ) : ℚ) / ((e : ℚ) ^ 6) := by
    rw [hx3, hyeq]; push_cast; field_simp
  unfold dblX
  rw [hnum, hden]
  push_cast
  field_simp
