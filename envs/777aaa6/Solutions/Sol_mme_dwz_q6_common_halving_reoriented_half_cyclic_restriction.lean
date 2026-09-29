-- Prove2me | solution 1 for mme_dwz_q6_common_halving_reoriented_half_cyclic_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:55:07.756607+00:00
-- url     : https://prove2.me/submissions/f7f115dd-eff4-40d7-b416-d66382691053

import Theorems.Thm_mme_dwz_q6_common_halving_union_word_projection_restriction
import Theorems.Thm_mme_tensor_basis_cartesian_projection_factorization
import Theorems.Thm_mme_cyclicSymmetrization_independent_factor_rotations
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap

open MME MME.DWZComponentRestriction Module TensorProduct
universe u
set_option autoImplicit false

/-- After cyclic symmetrization, the retained halves can be independently
rotated back toward their original coupled orientation, keeping the full
numeric tensor on each allowed half-word. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let left := (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N
    let right := (TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N
    let bX := kronPowModeBasis
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let bY := kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x => Sum.elim (fun _ => 0) (fun _ => 1) x.down
    let keepX := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N =>
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N =>
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w r) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    let f : ∀ i, left.V i →ₗ[K] left.V i :=
      Function.update (fun _ => LinearMap.id) 2
        (bX.constr K (fun w => if keepX w then bX w else 0))
    let g : ∀ i, right.V i →ₗ[K] right.V i :=
      Function.update (fun _ => LinearMap.id) 2
        (bY.constr K (fun w => if keepY w then bY w else 0))
    let X : TensorObj K 3 := { left with t := PiTensorProduct.map f left.t }
    let Y : TensorObj K 3 := { right with t := PiTensorProduct.map g right.t }
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.kron
        (TensorObj.permObj cyclicPerm X)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) Y)))
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  classical
  intro left right bX bY grade keepX keepY f g X Y
  letI : DecidablePred keepX := Classical.decPred _
  letI : DecidablePred keepY := Classical.decPred _
  letI : DecidablePred (fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ×
      PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N => keepX w.1 ∧ keepY w.2) :=
    Classical.decPred _
  have hp := mme_tensor_basis_cartesian_projection_factorization
    left right bX bY keepX keepY
  have h := mme_dwz_q6_common_halving_union_word_projection_restriction
    (K := K) s hs m hN family halving
  set_option backward.isDefEq.respectTransparency false in
    change TensorObj.Restrict
      { TensorObj.kron left right with t := (PiTensorProduct.map
        (Function.update (fun _ => LinearMap.id) 2
          ((bX.tensorProduct bY).constr K (fun w =>
            if keepX w.1 ∧ keepY w.2 then (bX.tensorProduct bY) w else 0)))
        (TensorObj.kron left right).t) }
      (componentPairRestricted K s m) at h
  erw [hp] at h
  set_option backward.isDefEq.respectTransparency false in
    change TensorObj.Restrict (TensorObj.kron X Y) (componentPairRestricted K s m) at h
  exact (mme_cyclicSymmetrization_independent_factor_rotations X Y).1.trans
    ((mme_cyclicSymmetrization_mono_restrict h).trans
      (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
        (restrictedComponentPower K s m)).2)

#print axioms solution
