-- Prove2me | solution 1 for MordellDenominators.dvd_den_dblX_of_dvd_den
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:23:35.034216+00:00
-- url     : https://prove2.me/submissions/fd0de09e-64f0-40e6-9745-00482fce21d7

-- Sol generated from Cryptography/MordellDenominators/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_dblX_eq_div
import Theorems.Thm_MordellDenominators_exists_den_param
import Theorems.Thm_MordellDenominators_ne_zero_of_dvd_den
import Theorems.Thm_MordellDenominators_prime_dvd_den_of_eq_div

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
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    {l : ℕ} (hl : l.Prime) (hd : l ∣ x.den) :
    l ∣ (dblX N x).den := by
  obtain ⟨e, he0, hxe, hye⟩ := exists_den_param h
  have hy : y ≠ 0 := ne_zero_of_dvd_den h hl hd
  have hb0 : y.num ≠ 0 := Rat.num_ne_zero.mpr hy
  have hle : (l : ℤ) ∣ (e : ℤ) := by
    have : l ∣ e := hl.dvd_of_dvd_pow (by rw [← hxe]; exact hd)
    exact_mod_cast this
  have hla : ¬ (l : ℤ) ∣ x.num := by
    intro hcon
    have h1 : l ∣ x.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hcon
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) hd
    exact hl.one_lt.ne' this
  have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast he0.ne'
  refine prime_dvd_den_of_eq_div (A := x.num ^ 4 - 8 * N * x.num * (e : ℤ) ^ 6)
    (B := 4 * y.num ^ 2 * (e : ℤ) ^ 2) (by positivity)
    (dblX_eq_div h he0 hxe hye hy) hl ?_ ?_
  · exact Dvd.dvd.mul_left (dvd_pow hle (by norm_num)) _
  · intro hcon
    have h6 : (l : ℤ) ∣ 8 * N * x.num * (e : ℤ) ^ 6 :=
      Dvd.dvd.mul_left (dvd_pow hle (by norm_num)) _
    have : (l : ℤ) ∣ x.num ^ 4 := by
      have := dvd_add hcon h6
      simpa using this
    exact hla ((Nat.prime_iff_prime_int.mp hl).dvd_of_dvd_pow this)
