-- Prove2me | Theorems.Thm_MordellDenominators_exists_den_param
-- name    : MordellDenominators.exists_den_param
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:55:50.820259+00:00
-- url     : https://prove2.me/theorems/a7941d70-19ba-4d75-8b5d-b5dacab1ecb6
-- title:
--   The classical shape of denominators on a Mordell curve: there is a positive
-- statement:
--   The classical shape of denominators on a Mordell curve: there is a positive
--   integer `e` with `x.den = e²` and `y.den = e³`.
--
--   ```lean
--   theorem MordellDenominators.exists_den_param{N : ℤ} {x y : ℚ} (h : OnCurve N x y) :
--       ∃ e : ℕ, 0 < e ∧ x.den = e ^ 2 ∧ y.den = e ^ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Basic.lean#L108

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



/-! ## The `(e², e³)` shape of denominators -/

theorem MordellDenominators.exists_den_param{N : ℤ} {x y : ℚ} (h : OnCurve N x y) :
    ∃ e : ℕ, 0 < e ∧ x.den = e ^ 2 ∧ y.den = e ^ 3 := by sorry
