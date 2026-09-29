-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
-- name    : mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:45:51.577577+00:00
-- url     : https://prove2.me/theorems/4ecb2b6f-fe53-4c80-a759-f749e52ac78e
-- title:
--   Cyclic symmetrization of equal-volume matrix sums has cubic count and volume
-- statement:
--   Let $K$ be a field and let $a_j,b_j,c_j$ be nonnegative matrix dimensions for $q$ summands, with common volume $a_jb_jc_j=v$. Cyclic symmetrization distributes over all ordered triples of summands: there are $Q=q^3$ matrix tensors such that
--   $$\operatorname{cyc}\!\left(\bigoplus_{j=1}^{q}\langle a_j,b_j,c_j\rangle\right)\cong\bigoplus_{r=1}^{Q}\langle A_r,B_r,C_r\rangle,\qquad A_rB_rC_r=v^3.$$
--   The isomorphism is mutual tensor restriction. The matrix dimensions may vary with the summand; only their volume is assumed constant. The result includes the empty sum and zero-volume cases.
-- source:
--   Cartesian Kronecker distribution over finite matrix sums, cyclic permutation of matrix dimensions, multiplicativity of matrix tensors, and the accepted restricted-pair coloring extraction and six-symmetrization paired-source identity.

import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Definitions.Def_mme_cyclicSymmetrization_public_perm
open MME MME.DWZComponentRestriction
universe u
set_option autoImplicit false

theorem mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
    {K : Type u} [Field K] {q v : ℕ} (a b c : Fin q → ℕ)
    (hvol : ∀ j, a j * b j * c j = v) :
    ∃ (Q : ℕ) (A B C : Fin Q → ℕ), Q = q ^ 3 ∧
      TensorObj.Isomorphic
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        (cyclicSymmetrization (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) ∧
      ∀ j, A j * B j * C j = v ^ 3 := by sorry
