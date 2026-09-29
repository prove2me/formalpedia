-- Prove2me | Definitions.Def_MachineLearning_HilbertPolya_LowRankObstruction
-- name    : MachineLearning_HilbertPolya_LowRankObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:40.816813+00:00
-- url     : https://prove2.me/theorems/7338f9b9-8367-4a62-bea3-387a86ae50f5
-- title:
--   Aether Catalog definitions — MachineLearning_HilbertPolya_LowRankObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HilbertPolya.LowRankObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HilbertPolya/LowRankObstruction.lean by skeleton subtraction
import Mathlib

/-!
# Low-Rank Obstruction for Naive Arithmetic Kernels

We prove that the symmetric outer-product matrix `M_{ij} = u_i v_j + v_i u_j`
has rank at most 2 for any vectors `u, v`. This implies that the naive
prime-log kernel `K(p,q) = log(pq)/√(pq)` is rank ≤ 2 and therefore cannot
encode the spectral complexity of zeta truncations.

## Main Results

- `rank_vecMulVec_le_one`: `rank(u · vᵀ) ≤ 1`
- `rank_add_outer_le_two`: `rank(u·vᵀ + v·uᵀ) ≤ 2`
-/

open Matrix

noncomputable section

/-- The symmetric rank-1+1 matrix `M_{ij} = u_i · v_j + v_i · u_j`. -/
def symOuterProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => u i * v j + v i * u j

/-
A rank-one outer product `u · vᵀ` has rank at most 1.
-/

/-
**The symmetric outer-product matrix has rank ≤ 2.**
    `rank(u·vᵀ + v·uᵀ) ≤ 2` for any vectors `u, v`.
-/

/-
The symmetric outer-product is indeed a sum of two outer products.
-/

end


