-- Prove2me | solution 1 for MordellDenominators.dvd_den_dblIter_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:25:26.766025+00:00
-- url     : https://prove2.me/submissions/345ebb1e-c810-4a30-a444-abd934a10018

-- Sol generated from Cryptography/MordellDenominators/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_dblIter_onCurve
import Theorems.Thm_MordellDenominators_dvd_den_dblX_of_dvd_den

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
theorem solution{N : ℤ} (hnt : ∀ x y : ℚ, OnCurve N x y → y ≠ 0)
    {P : ℚ × ℚ} (h : OnCurve N P.1 P.2) {l : ℕ} (hl : l.Prime) {n : ℕ}
    (hd : l ∣ (dblIter N n P).1.den) :
    ∀ m : ℕ, l ∣ (dblIter N (n + m) P).1.den := by
  intro m
  induction m with
  | zero => simpa using hd
  | succ k ih =>
      have hstep : dblIter N (n + k + 1) P = dbl N (dblIter N (n + k) P) := by
        simp [dblIter, Function.iterate_succ_apply']
      have : n + (k + 1) = n + k + 1 := by ring
      rw [this, hstep]
      exact dvd_den_dblX_of_dvd_den (dblIter_onCurve hnt h (n + k)) hl ih
