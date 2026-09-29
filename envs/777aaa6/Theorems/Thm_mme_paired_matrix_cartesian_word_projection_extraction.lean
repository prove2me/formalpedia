-- Prove2me | Theorems.Thm_mme_paired_matrix_cartesian_word_projection_extraction
-- name    : mme_paired_matrix_cartesian_word_projection_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:56:36.541251+00:00
-- url     : https://prove2.me/theorems/0a32148e-25c9-4adc-881b-4e909404a0fd
-- title:
--   Cartesian word selections extract a matrix block of the selected cardinalities
-- statement:
--   Let $K$ be a field and $q,N$ be natural numbers. Take the tensor product of the $N$th powers of the two cyclic orientations of the matrix multiplication tensor $\langle1,q,1\rangle$. Select arbitrary sets $X,Y$ of labels in their respective third-coordinate word bases. Retain exactly the paired basis vectors indexed by $X\times Y$. The projected tensor restricts to $\langle |X|,1,|Y|\rangle$. This includes empty selections and $N=0$.
-- source:
--   Composition of word-basis-preserving matrix flattening with a rectangular coordinate restriction.

import Theorems.Thm_mme_paired_oriented_matrix_power_word_basis_maps
import Theorems.Thm_mme_MMObj_rectangle_mask_cardinality_restriction
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.LinearAlgebra.StdBasis

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u v
set_option autoImplicit false

theorem mme_paired_matrix_cartesian_word_projection_extraction
    {K : Type u} [Field K] (q N : ℕ)
    (keepX : PowIndex (ULift.{u} (Fin 1 × Fin q)) N → Prop)
    (keepY : PowIndex (ULift.{u} (Fin q × Fin 1)) N → Prop)
    [DecidablePred keepX] [DecidablePred keepY] :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 q 1)
    let c := (Pi.basisFun K (Fin 1 × Fin q)).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin q × Fin 1)).reindex Equiv.ulift.symm
    let B := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let source := (U.kronPow N).kron (V.kronPow N)
    let P : ∀ i, source.V i →ₗ[K] source.V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (B.constr K (fun w ↦ if keepX w.1 ∧ keepY w.2 then B w else 0))
    TensorObj.Restrict
      (MMObj K (Fintype.card {x // keepX x}) 1 (Fintype.card {y // keepY y}))
      { source with t := PiTensorProduct.map P source.t } := by sorry
