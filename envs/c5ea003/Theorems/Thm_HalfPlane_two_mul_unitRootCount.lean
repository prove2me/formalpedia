-- Prove2me | Theorems.Thm_HalfPlane_two_mul_unitRootCount
-- name    : HalfPlane.two_mul_unitRootCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:23:15.332033+00:00
-- url     : https://prove2.me/theorems/55e5e6fa-a430-4389-9d15-33fdd7252989
-- title:
--   The antipodal pairing on square roots of one: exactly half of them lie below
-- statement:
--   **The antipodal pairing on square roots of one**: exactly half of them lie below
--   `N/2`, so `2 R(N) = S(N)` for `N ≥ 3`.
--
--   ```lean
--   theorem HalfPlane.two_mul_unitRootCount(N : ℕ) (hN : 3 ≤ N) :
--       2 * unitRootCount N = sqrtOneCount N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneSemiprime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneSemiprime.lean#L122

-- Thm stub generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

/-!
# The correction term is separable, and the semiprime circle count

Cycle 2 of the investigation.  The reflection identity of `HalfPlaneReflection.lean`
writes the non-separable half-plane count as

  `H(N) = high(N) + 2 R(N)`,

with `R(N)` the number of square roots of `1` below `N/2`.  Here we show that the
correction term `R` is itself completely *local*:

* `two_mul_unitRootCount` : `2 R(N) = S(N)` for `N ≥ 3`, where `S(N)` is the total
  number of square roots of `1` modulo `N` (the antipodal pairing `u ↦ N - u` has no
  fixed point on the roots once `N ≥ 3`);
* `sqrtOneCount_mul_of_coprime` : `S` is multiplicative.

So *all* of the non-separability of `H` is carried by the corner count `high`.

We then push the separable side to its arithmetic conclusion:

* `circleCount_semiprime` : `C(pq) = (p - χ_p(-1))(q - χ_q(-1))` for distinct odd
  primes;
* `circleCount_semiprime_three_mod_four` : if `p ≡ q ≡ 3 (mod 4)` then
  `C(pq) = pq + p + q + 1`, hence
* `sum_of_primes_from_circleCount` : `p + q = C(N) - N - 1` — the circle count of a
  Blum-type semiprime *determines the factorisation*.  The obstruction is purely
  computational: evaluating `C(N)` by enumeration costs `Θ(N)` steps.
-/

open HalfPlane

open Finset

/-! ### Square roots of one -/

theorem HalfPlane.two_mul_unitRootCount(N : ℕ) (hN : 3 ≤ N) :
    2 * unitRootCount N = sqrtOneCount N := by sorry
