-- Prove2me | Theorems.Thm_mme_six_square_family_product_weight
-- name    : mme_six_square_family_product_weight
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:30:38.84853+00:00
-- url     : https://prove2.me/theorems/4b2f15a2-c1a7-44f2-b08d-0caea55f343a
-- title:
--   Boundary square extraction multiplies an interior matrix family
-- statement:
--   An actual square matrix extraction from the six-fold symmetrization of X and an actual matrix-family extraction from the six-fold symmetrization of Y combine into an extraction from the six-fold symmetrization of their Kronecker product. Each interior matrix dimension is multiplied by the boundary side length, and the number of summands is preserved exactly. If the two tau-weights are at least exp(boundaryRate) and exp(interiorRate), the combined tau-weight is at least exp(boundaryRate + interiorRate), for any real tau.
-- source:
--   Exact tensor distributivity and multiplicativity of nonnegative real powers.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
open MME BigOperators
set_option autoImplicit false
universe u

theorem mme_six_square_family_product_weight
    {K : Type u} [Field K] {X Y : TensorObj K 3} {q : ℕ}
    (M : ℕ) (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ)
    (hboundary : TensorObj.Restrict (MMObj K M M M) (sixSymmetrization X))
    (hinterior : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) (sixSymmetrization Y))
    (hboundaryWeight : Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau)
    (hinteriorWeight : Real.exp interiorRate ≤
      ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (sixSymmetrization (TensorObj.kron X Y)) ∧
    Real.exp (boundaryRate + interiorRate) ≤
      ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by sorry
