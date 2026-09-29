-- Prove2me | Theorems.Thm_mme_coupled_paired_trace_source_word_projection_restriction
-- name    : mme_coupled_paired_trace_source_word_projection_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:08:07.127029+00:00
-- url     : https://prove2.me/theorems/cae4f7ff-f9d3-4b6a-96c5-42b6a1477a74
-- title:
--   Every coupled word-pair selection transfers through paired trace
-- statement:
--   Let $K$ be any field and $q,N$ nonnegative integers. Take the $N$th powers of the two cyclic orientations of the coupled constituent $C_q$ and pair them. Retain any chosen set of third-coordinate word pairs by its basis projection. This projected source restricts to the corresponding projected pair of cyclic matrix-tensor powers of $\langle1,2q,1\rangle$. The surviving target labels are specified by inverse trace maps: position by position, undo the enumeration $e:\operatorname{Fin}(q)\sqcup\operatorname{Fin}(q)\simeq\operatorname{Fin}(2q)$; in the second word also undo the label swap. These inverse maps recover every source word exactly, including the empty word. The selected set is arbitrary and may contain all Cartesian cross-pairs. The result preserves the full numerical letters but does not identify the projected target as a flattened matrix block or compute its volume.
-- source:
--   Explicit paired trace basis maps, inverse word-label identities, and transport of basis projections.

import Definitions.Def_mme_permutation
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_coupled_paired_trace_source_word_projection_restriction
    {K : Type u} [Field K] (q N : ℕ)
    (keep : (PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ×
      PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N) → Prop)
    [DecidablePred keep] :
    let L := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)
    let R := TensorObj.permObj cyclicPerm (coupledObj K q)
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (q + q) 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 (q + q) 1)
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (q + q))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin q ⊕ Fin q)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (q + q) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin q ⊕ Fin q)))
    let B := (kronPowModeBasis L 2 b N).tensorProduct (kronPowModeBasis R 2 b N)
    let C := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let source := (L.kronPow N).kron (R.kronPow N)
    let target := (U.kronPow N).kron (V.kronPow N)
    TensorObj.Restrict
      { target with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (C.constr K (fun w ↦ if keep (h0 w.1, h1 w.2) then C w else 0))) target.t) }
      { source with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (B.constr K (fun w ↦ if keep w then B w else 0))) source.t) } := by sorry
