-- Prove2me | Theorems.Thm_mme_sixSymmetrization_aggregate_matrix_extraction
-- name    : mme_sixSymmetrization_aggregate_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:17:16.569676+00:00
-- url     : https://prove2.me/theorems/090b6482-4772-433a-869b-75e7142e6ca0
-- title:
--   An aggregate paired matrix block pays quadratic multiplicity above exponent two thirds
-- statement:
--   Let T be a three-tensor over a field. Suppose its paired tensor T tensor swap(T) restricts to a matrix multiplication tensor of dimensions n,m,p with nmp=Hv and H>=1. For every real exponent tau>=2/3, the sixfold symmetrization of T restricts to the square matrix multiplication tensor of dimensions Hv,Hv,Hv, and H^2 (v^3)^tau <= ((Hv)^3)^tau. The theorem assumes the aggregate matrix restriction; it does not construct that restriction from a primary hash family.
-- source:
--   Cyclic symmetrization of a matrix multiplication tensor and monotonicity of real powers in the exponent.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MME
universe u
set_option autoImplicit false

theorem mme_sixSymmetrization_aggregate_matrix_extraction
    {K : Type u} [Field K] (T : TensorObj K 3)
    (n m p H v : ℕ) (hH : 1 ≤ H) (hvolume : n * m * p = H * v)
    (tau : ℝ) (htau : (2 : ℝ) / 3 ≤ tau)
    (hrestrict : TensorObj.Restrict (MMObj K n m p)
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) :
    TensorObj.Restrict (MMObj K (H * v) (H * v) (H * v))
      (sixSymmetrization T) ∧
    (H : ℝ) ^ 2 * ((v ^ 3 : ℕ) : ℝ) ^ tau ≤
      (((H * v) ^ 3 : ℕ) : ℝ) ^ tau := by sorry
