-- Prove2me | Theorems.Thm_HalfPlane_sqrtOneCount_eq_card_sqrtOneZ
-- name    : HalfPlane.sqrtOneCount_eq_card_sqrtOneZ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:23:01.6098+00:00
-- url     : https://prove2.me/theorems/122b50a6-f070-4804-9992-d05b93b70bca
-- title:
--   SqrtOneCount eq card sqrtOneZ
-- statement:
--   Formal statement of `HalfPlane.sqrtOneCount_eq_card_sqrtOneZ` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HalfPlane.sqrtOneCount_eq_card_sqrtOneZ(N : ℕ) [NeZero N] :
--       sqrtOneCount N = (sqrtOneZ N).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneSemiprime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneSemiprime.lean#L52

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

theorem HalfPlane.sqrtOneCount_eq_card_sqrtOneZ(N : ℕ) [NeZero N] :
    sqrtOneCount N = (sqrtOneZ N).card := by sorry
