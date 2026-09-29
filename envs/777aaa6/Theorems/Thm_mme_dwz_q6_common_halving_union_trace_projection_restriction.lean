-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_union_trace_projection_restriction
-- name    : mme_dwz_q6_common_halving_union_trace_projection_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:11:28.470957+00:00
-- url     : https://prove2.me/theorems/098a45c8-ee14-45c6-8ed3-c10e1a9676fb
-- title:
--   Trace transfers the common-halving word union to paired matrix powers
-- statement:
--   Let $K$ be any field, $s\in\{13,14\}$, $N=c_s m$, and let a $q=6$ primary hash family admit a common balanced XY halving. The literal restricted component pair restricts to a third-coordinate projection of the paired $N$th powers of the two cyclic orientations of $\langle1,12,1\rangle$. The retained matrix word pairs are exactly those whose inverse trace labels belong to the union of the family's first-half X words and the union of its second-half Y words. Each inverse label first undoes the enumeration of the two copies of $\operatorname{Fin}(6)$; the second word also undoes the binary-label swap. The two existential family witnesses are independent, so all cross-pairs in the Cartesian product of the two unions remain. This is an unconditional projected-tensor restriction for every family with the stated halving. It does not yet identify a flattened matrix block or establish the volume required by the full finite-extraction theorem.
-- source:
--   Composition of the accepted common-halving union-word restriction with explicit paired trace basis maps and basis-projection transport.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_dwz_component_pair_projection_data
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

theorem mme_dwz_q6_common_halving_union_trace_projection_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (6 + 6) 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 (6 + 6) 1)
    let c := (Pi.basisFun K (Fin 1 × Fin (6 + 6))).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin (6 + 6) × Fin 1)).reindex Equiv.ulift.symm
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (6 + 6))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin 6 ⊕ Fin 6)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (6 + 6) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin 6 ⊕ Fin 6)))
    let C := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let target := (U.kronPow N).kron (V.kronPow N)
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    let allowed := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ×
        PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ↦
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.1 r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))) ∧
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.2 r) =
          (family.entry p).val 1 (halving.position (Sum.inr r)))
    letI : DecidablePred allowed := Classical.decPred _
    TensorObj.Restrict
      { target with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (C.constr K (fun w ↦ if allowed (h0 w.1, h1 w.2) then C w else 0))) target.t) }
      (componentPairRestricted K s m) := by sorry
