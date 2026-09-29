-- Prove2me | Definitions.Def_MachineLearning_CayleyCensusMoments
-- name    : MachineLearning_CayleyCensusMoments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T15:42:19.479375+00:00
-- url     : https://prove2.me/theorems/fd7bb135-811d-4e0e-a930-ec9fe4707f8b
-- title:
--   Aether Catalog definitions — MachineLearning_CayleyCensusMoments
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CayleyCensusMoments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CayleyCensusMoments.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance

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

namespace CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]


/-! ### The concatenation (semigroup) law -/




/-! ### The adjacency-matrix bridge -/

/-- The adjacency matrix of the Cayley graph `Cay(G, S)`: there is an edge from
`x` to `y` exactly when `x⁻¹ y ∈ S`. -/
def adj (S : Finset G) : Matrix G G ℕ := fun x y => if x⁻¹ * y ∈ S then 1 else 0





end CayleyCensus


