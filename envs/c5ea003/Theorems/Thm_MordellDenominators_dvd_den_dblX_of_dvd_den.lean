-- Prove2me | Theorems.Thm_MordellDenominators_dvd_den_dblX_of_dvd_den
-- name    : MordellDenominators.dvd_den_dblX_of_dvd_den
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:55:53.123071+00:00
-- url     : https://prove2.me/theorems/0d8f8283-a91d-48c2-adbe-dcca7a26a83f
-- title:
--   The kernel of reduction is stable under duplication.
-- statement:
--   **The kernel of reduction is stable under duplication.**  If a prime `ℓ`
--   divides the denominator of `x(P)` for a rational point `P` on `E_N`, then it
--   divides the denominator of `x(2P)` as well.  Hence a prime that appears once in
--   the orbit appears in every later doubling.
--
--   ```lean
--   theorem MordellDenominators.dvd_den_dblX_of_dvd_den{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
--       {l : ℕ} (hl : l.Prime) (hd : l ∣ x.den) :
--       l ∣ (dblX N x).den := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Basic.lean#L250

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







/-! ## The duplication formula -/


/-! ## Stability of the kernel of reduction under duplication -/

theorem MordellDenominators.dvd_den_dblX_of_dvd_den{N : ℤ} {x y : ℚ} (h : OnCurve N x y)
    {l : ℕ} (hl : l.Prime) (hd : l ∣ x.den) :
    l ∣ (dblX N x).den := by sorry
