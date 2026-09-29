-- Prove2me | solution 1 for MordellDenominators.exists_den_param
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:23.57138+00:00
-- url     : https://prove2.me/submissions/8fb7902c-f394-4fde-a93f-ed00061a5502

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

/-- For a rational point on `y² = x³ + N` with `N` an integer, the denominators
satisfy `den(y)² = den(x)³`. -/
theorem den_sq_eq_den_cube {N : ℤ} {x y : ℚ} (h : OnCurve N x y) :
    y.den ^ 2 = x.den ^ 3 := by
  have h1 : (y ^ 2).den = (x ^ 3 + (N : ℚ)).den := by rw [h]
  rwa [Rat.den_pow, Rat.add_intCast_den, Rat.den_pow] at h1






/-! ## The duplication formula -/


/-! ## Stability of the kernel of reduction under duplication -/




/-! ## Orbits under duplication -/






open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) :
    ∃ e : ℕ, 0 < e ∧ x.den = e ^ 2 ∧ y.den = e ^ 3 := by
  have hkey := den_sq_eq_den_cube h
  have hx0 : 0 < x.den := x.pos
  have hdvd2 : x.den ^ 2 ∣ y.den ^ 2 := by
    rw [hkey]; exact pow_dvd_pow _ (by norm_num)
  have hdvd : x.den ∣ y.den := (Nat.pow_dvd_pow_iff (two_ne_zero)).mp hdvd2
  obtain ⟨e, he⟩ := hdvd
  have hcancel : x.den ^ 2 * e ^ 2 = x.den ^ 2 * x.den :=
    calc x.den ^ 2 * e ^ 2 = (x.den * e) ^ 2 := by ring
      _ = y.den ^ 2 := by rw [he]
      _ = x.den ^ 3 := hkey
      _ = x.den ^ 2 * x.den := by ring
  have hxe : x.den = e ^ 2 := (Nat.eq_of_mul_eq_mul_left (by positivity) hcancel).symm
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h' 
    · simp [hxe] at hx0
    · exact h'
  exact ⟨e, he0, hxe, by rw [he, hxe]; ring⟩
