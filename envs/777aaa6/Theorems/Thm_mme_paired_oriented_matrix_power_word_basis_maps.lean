-- Prove2me | Theorems.Thm_mme_paired_oriented_matrix_power_word_basis_maps
-- name    : mme_paired_oriented_matrix_power_word_basis_maps
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:35:38.094723+00:00
-- url     : https://prove2.me/theorems/a6c056ae-c146-4782-87ab-605b08cf9701
-- title:
--   Paired oriented matrix powers have independent row and column word labels
-- statement:
--   Let $K$ be a field and $q,N$ be natural numbers. Let $U$ and $V$ be the two cyclic orientations of the matrix multiplication tensor $\langle1,q,1\rangle$, with dimensions $\langle q,1,1\rangle$ and $\langle1,1,q\rangle$, respectively. There are mode-wise linear maps carrying
--   $$U^{\otimes N}\otimes V^{\otimes N}\quad\text{to}\quad\langle q^N,1,q^N\rangle.$$
--   Moreover, there are independent bijections $c$ and $r$ from the complete third-coordinate word bases of $U^{\otimes N}$ and $V^{\otimes N}$ to the column and row index sets. The third mode map satisfies
--   $$e_x\otimes e_y\longmapsto e_{r(y),c(x)}.$$
--   This identifies how Cartesian selections of the two word sets become row and column selections in the flattened matrix tensor. The result includes $N=0$ and $q=0$.
-- source:
--   Cyclic basis maps, the accepted matrix-power word-basis theorem, and the explicit matrix Kronecker equivalence.

import Theorems.Thm_mme_MMObj_power_third_word_basis_maps
import Definitions.Def_mme_permutation
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_paired_oriented_matrix_power_word_basis_maps
    {K : Type u} [Field K] (q N : ℕ) :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 q 1)
    let c := (Pi.basisFun K (Fin 1 × Fin q)).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin q × Fin 1)).reindex Equiv.ulift.symm
    ∃ F : ∀ i, ((U.kronPow N).kron (V.kronPow N)).V i →ₗ[K]
        (MMObj K (q^N) 1 (q^N)).V i,
    ∃ rows : PowIndex (ULift.{u} (Fin q × Fin 1)) N ≃ Fin (q^N),
    ∃ cols : PowIndex (ULift.{u} (Fin 1 × Fin q)) N ≃ Fin (q^N),
      PiTensorProduct.map F ((U.kronPow N).kron (V.kronPow N)).t =
        (MMObj K (q^N) 1 (q^N)).t ∧
      ∀ x y, F 2 ((kronPowModeBasis U 2 c N x) ⊗ₜ[K]
          (kronPowModeBasis V 2 e N y)) = Pi.single (rows y, cols x) 1 := by sorry
