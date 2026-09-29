-- Prove2me | Theorems.Thm_mme_sixSymmetrization_aggregate_family_finite_extraction
-- name    : mme_sixSymmetrization_aggregate_family_finite_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:18:37.525703+00:00
-- url     : https://prove2.me/theorems/e883dee0-2475-4c78-b632-8e92ed4fec53
-- title:
--   Aggregate matrix blocks recover cubic outer and quadratic inner multiplicity
-- statement:
--   Let $T$ be a three-tensor over a field, let $A,H,v$ be natural numbers with $H\geq1$, and let $\tau\geq2/3$. Suppose $T\otimes\operatorname{swap}_{12}(T)$ restricts to a direct sum of $A$ matrix multiplication tensors, each of volume $Hv$. Then the sixfold symmetrization of $T$ restricts to a finite direct sum of matrix multiplication tensors with dimensions $(a_j,b_j,c_j)$ satisfying
--   $$A^3H^2(v^3)^\tau\leq\sum_j(a_jb_jc_j)^\tau.$$
--   Thus retaining an aggregate matrix block in each outer fiber suffices to recover the cubic outer multiplicity and quadratic inner multiplicity. The aggregate restriction is a hypothesis; the result does not assert its existence for arbitrary hash families.
-- source:
--   Cyclic symmetrization of a uniform-volume matrix direct sum, the paired-swap identity, and monotonicity of real powers.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MME
universe u
set_option autoImplicit false

theorem mme_sixSymmetrization_aggregate_family_finite_extraction
    {K : Type u} [Field K] (T : TensorObj K 3)
    (A H v : ℕ) (hH : 1 ≤ H) (tau : ℝ) (htau : (2 : ℝ) / 3 ≤ tau)
    (a b c : Fin A → ℕ) (hvolume : ∀ i, a i * b i * c i = H * v)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) :
    ∃ (Q : ℕ) (a' b' c' : Fin Q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization T) ∧
      (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * ((v ^ 3 : ℕ) : ℝ) ^ tau ≤
        ∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau) := by sorry
