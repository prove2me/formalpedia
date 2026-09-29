-- Prove2me | solution 1 for MordellDenominators.ne_zero_of_dvd_den
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:20:15.712395+00:00
-- url     : https://prove2.me/submissions/09b0aa4f-0520-4ea5-b69b-8d424542bd40

-- Sol generated from Cryptography/MordellDenominators/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_exists_den_param

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
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
    (hl : l.Prime) (hd : l ∣ x.den) : y ≠ 0 := by
  obtain ⟨e, he0, hxe, hye⟩ := exists_den_param h
  intro hy0
  have hy1 : y.den = 1 := by rw [hy0]; rfl
  rw [hye] at hy1
  have he1 : e = 1 := by
    have := Nat.pow_eq_one.mp hy1
    tauto
  have hx1 : x.den = 1 := by rw [hxe, he1]; norm_num
  rw [hx1] at hd
  exact hl.one_lt.ne' (Nat.dvd_one.mp hd)
