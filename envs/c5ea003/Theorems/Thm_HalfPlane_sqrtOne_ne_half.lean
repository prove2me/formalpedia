-- Prove2me | Theorems.Thm_HalfPlane_sqrtOne_ne_half
-- name    : HalfPlane.sqrtOne_ne_half
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:23:37.934202+00:00
-- url     : https://prove2.me/theorems/1524e513-9764-4597-a6d9-b1c2c7c1bf6f
-- title:
--   A square root of `1` is never equal to `N/2` (for `N ≥ 3`): the antipodal pairing
-- statement:
--   A square root of `1` is never equal to `N/2` (for `N ≥ 3`): the antipodal pairing
--   on the roots is fixed-point free.
--
--   ```lean
--   theorem HalfPlane.sqrtOne_ne_half{N u : ℕ} (hN : 3 ≤ N) (hu : u ^ 2 % N = 1 % N) : 2 * u ≠ N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneSemiprime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneSemiprime.lean#L103

-- Thm stub generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
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

theorem HalfPlane.sqrtOne_ne_half{N u : ℕ} (hN : 3 ≤ N) (hu : u ^ 2 % N = 1 % N) : 2 * u ≠ N := by sorry
