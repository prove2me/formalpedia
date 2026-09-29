-- Prove2me | solution 1 for MordellDenominators.dblIter_onCurve
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:22.039859+00:00
-- url     : https://prove2.me/submissions/3bfb83bb-196f-4f31-bffd-5d8c6cd417e7

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

/-- Duplication sends a rational point with `y ≠ 0` to a rational point. -/
theorem dbl_onCurve {N : ℤ} {x y : ℚ} (h : OnCurve N x y) (hy : y ≠ 0) :
    OnCurve N (dblX N x) (dblY N x y) := by
  have hN : (N : ℚ) = y ^ 2 - x ^ 3 := by
    have := h; unfold OnCurve at this; linarith
  unfold OnCurve dblY dblX
  rw [hN]
  have h4 : (4 : ℚ) * (x ^ 3 + (y ^ 2 - x ^ 3)) ≠ 0 := by
    have h2 : y ^ 2 ≠ 0 := pow_ne_zero _ hy
    intro hc; apply h2; nlinarith [hc]
  field_simp
  ring

/-! ## Stability of the kernel of reduction under duplication -/




/-! ## Orbits under duplication -/






open MordellDenominators in
theorem solution{N : ℤ} (hnt : ∀ x y : ℚ, OnCurve N x y → y ≠ 0)
    {P : ℚ × ℚ} (h : OnCurve N P.1 P.2) :
    ∀ n : ℕ, OnCurve N (dblIter N n P).1 (dblIter N n P).2 := by
  intro n
  induction n with
  | zero => simpa [dblIter] using h
  | succ k ih =>
      have : dblIter N (k + 1) P = dbl N (dblIter N k P) := by
        simp [dblIter, Function.iterate_succ_apply']
      rw [this]
      exact dbl_onCurve ih (hnt _ _ ih)
