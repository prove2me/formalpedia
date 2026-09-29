-- Prove2me | Theorems.Thm_CayleyCensus_adj_isSymm
-- name    : CayleyCensus.adj_isSymm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:38:41.795224+00:00
-- url     : https://prove2.me/theorems/78cb5818-9b39-42c7-a8a0-176f7c74b51a
-- title:
--   Inversion-closedness of the connection set is precisely symmetry of the
-- statement:
--   Inversion-closedness of the connection set is precisely symmetry of the
--   adjacency matrix; this is the linear-algebraic shadow of `walkCount_inv`.
--
--   ```lean
--   theorem CayleyCensus.adj_isSymm{S : Finset G} (hS : InvClosed S) : (adj S).IsSymm := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CayleyCensusMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CayleyCensusMoments.lean#L131

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




/-! ### The adjacency-matrix bridge -/



omit [Fintype G] in

theorem CayleyCensus.adj_isSymm{S : Finset G} (hS : InvClosed S) : (adj S).IsSymm := by sorry
