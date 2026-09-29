-- Prove2me | Theorems.Thm_CayleyCensus_walkCount_two_mul_le_walkCount_two_mul_one
-- name    : CayleyCensus.walkCount_two_mul_le_walkCount_two_mul_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:43:33.359867+00:00
-- url     : https://prove2.me/theorems/ce5bb741-46ad-4148-adba-8011575f8149
-- title:
--   Return dominance.
-- statement:
--   **Return dominance.**  For an inversion-closed connection set the even-length
--   census is maximised at the identity.  The two ingredients are the inversion
--   symmetry of the census and the elementary inequality `2ab ≤ a² + b²`.
--
--   ```lean
--   theorem CayleyCensus.walkCount_two_mul_le_walkCount_two_mul_one{S : Finset G} (hS : InvClosed S)
--       (n : ℕ) (g : G) : walkCount S (2 * n) g ≤ walkCount S (2 * n) (1 : G) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CayleyCensusMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CayleyCensusMoments.lean#L89

-- Thm stub generated from MachineLearning/CayleyCensusMoments.lean
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

/-!
# Moments, adjacency powers and return dominance for the Cayley census

This file is the analytic/linear-algebraic half of the census project begun in
`Catalog.MachineLearning.CayleyCensusInvariance`.  Three layers are built on top
of the invariance results proved there.

1. **Concatenation (Chapman–Kolmogorov).**  `walkCount_add` expresses
   `walkCount S (m + n) g` as a convolution of two shorter censuses.  This is
   the semigroup law of the census, and it is what makes the census a *moment
   sequence* rather than a mere counting function.

2. **Return dominance.**  `walkCount_two_mul_le_walkCount_two_mul_one`:
   for an inversion-closed connection set the even-length census is maximised at
   the identity, `walkCount S (2n) g ≤ walkCount S (2n) 1`.  The proof genuinely
   *uses* the inversion symmetry (`walkCount_inv`) — without it the statement is
   false for directed connection sets — combined with the discrete
   Cauchy–Schwarz inequality `2ab ≤ a² + b²` over `ℕ`.
   The identity `walkCount_two_mul_one_eq_sum_sq`,
   `walkCount S (2n) 1 = ∑ h, walkCount S n h ^ 2`, is the second-moment form.

3. **Adjacency bridge.**  `walkCount_eq_adj_pow` identifies the census with
   entries of powers of the Cayley adjacency matrix, `adj_isSymm` shows that
   inversion-closedness is exactly symmetry of that matrix, and `trace_adj_pow`
   gives the trace formula `tr(Aⁿ) = |G| · walkCount S n 1`, the discrete
   analogue of a heat-kernel trace.

## Main results

* `walkCount_add`
* `walkCount_two_mul_one_eq_sum_sq`
* `walkCount_two_mul_le_walkCount_two_mul_one`
* `walkCount_eq_adj_pow`, `adj_isSymm`, `trace_adj_pow`
-/

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]


/-! ### The concatenation (semigroup) law -/

theorem CayleyCensus.walkCount_two_mul_le_walkCount_two_mul_one{S : Finset G} (hS : InvClosed S)
    (n : ℕ) (g : G) : walkCount S (2 * n) g ≤ walkCount S (2 * n) (1 : G) := by sorry
