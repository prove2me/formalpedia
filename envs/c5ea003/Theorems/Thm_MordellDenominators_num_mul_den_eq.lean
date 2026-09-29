-- Prove2me | Theorems.Thm_MordellDenominators_num_mul_den_eq
-- name    : MordellDenominators.num_mul_den_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:55:59.463499+00:00
-- url     : https://prove2.me/theorems/9ac72520-dfe6-49e2-a6f6-ec28a65e4b89
-- title:
--   The cross-multiplication identity for a rational written as `A / B`.
-- statement:
--   The cross-multiplication identity for a rational written as `A / B`.
--
--   ```lean
--   theorem MordellDenominators.num_mul_den_eq{q : ℚ} {A B : ℤ} (hB : B ≠ 0)
--       (hq : q = (A : ℚ) / (B : ℚ)) : q.num * B = A * (q.den : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Basic.lean#L74

-- Thm stub generated from Cryptography/MordellDenominators/Basic.lean
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

theorem MordellDenominators.num_mul_den_eq{q : ℚ} {A B : ℤ} (hB : B ≠ 0)
    (hq : q = (A : ℚ) / (B : ℚ)) : q.num * B = A * (q.den : ℤ) := by sorry
