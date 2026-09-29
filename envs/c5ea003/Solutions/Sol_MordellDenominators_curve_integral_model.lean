-- Prove2me | solution 1 for MordellDenominators.curve_integral_model
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:21.456735+00:00
-- url     : https://prove2.me/submissions/5a5d54c6-573b-4920-a1b2-30c9e888720b

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
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {e : ℕ}
    (hxe : x.den = e ^ 2) (hye : y.den = e ^ 3) :
    y.num ^ 2 = x.num ^ 3 + N * (e : ℤ) ^ 6 := by
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h'
    · exfalso; simp at hxe
    · exact h'
  have hex : (e : ℚ) ≠ 0 := by exact_mod_cast he0.ne'
  have hx : x * (e : ℚ) ^ 2 = (x.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den x, hxe]
    push_cast
    field_simp
  have hy : y * (e : ℚ) ^ 3 = (y.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den y, hye]
    push_cast
    field_simp
  have hcurve : y ^ 2 = x ^ 3 + (N : ℚ) := h
  have : ((y.num ^ 2 : ℤ) : ℚ) = ((x.num ^ 3 + N * (e : ℤ) ^ 6 : ℤ) : ℚ) := by
    push_cast
    rw [← hx, ← hy]
    calc (y * (e : ℚ) ^ 3) ^ 2 = y ^ 2 * (e : ℚ) ^ 6 := by ring
      _ = (x ^ 3 + (N : ℚ)) * (e : ℚ) ^ 6 := by rw [hcurve]
      _ = (x * (e : ℚ) ^ 2) ^ 3 + (N : ℚ) * (e : ℚ) ^ 6 := by ring
  exact_mod_cast this
