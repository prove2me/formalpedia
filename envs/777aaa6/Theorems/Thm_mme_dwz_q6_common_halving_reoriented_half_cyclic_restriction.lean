-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_reoriented_half_cyclic_restriction
-- name    : mme_dwz_q6_common_halving_reoriented_half_cyclic_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:54:40.166995+00:00
-- url     : https://prove2.me/theorems/ca16fc8a-2068-4e27-9f89-ef6f36279faa
-- title:
--   Cyclic restriction to reoriented allowed half-word tensors
-- statement:
--   Fix a primary coupled-address family with a common balanced halving, and take row 13 or 14 of the DWZ component table, with half-length $N=c_s m$. Let $C$ be the coupled tensor at parameter 6 and let $\rho$ cyclically permute the three modes. In $(\rho^2 C)^{\otimes N}$ retain precisely the third-mode basis words whose binary grades occur as first-half X words of the family; call the resulting tensor $X$. Likewise, in $(\rho C)^{\otimes N}$ retain the third-mode words whose grades occur as second-half Y words; call this tensor $Y$. Then
--   $$\operatorname{cyc}(\rho X\otimes\rho^2Y)\preceq\operatorname{six}(R_{s,m}),$$
--   where $R_{s,m}$ is the restricted component power and $\preceq$ denotes tensor restriction. The projections preserve all numeric coordinates associated with the allowed words. This gives a source for further extraction after cyclic regrouping.
-- source:
--   Consequence of the common-halving union-word source restriction, Cartesian projection factorization, and independent cyclic factor rotations.

import Theorems.Thm_mme_dwz_q6_common_halving_union_word_projection_restriction
import Theorems.Thm_mme_tensor_basis_cartesian_projection_factorization
import Theorems.Thm_mme_cyclicSymmetrization_independent_factor_rotations
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap

open MME MME.DWZComponentRestriction Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_reoriented_half_cyclic_restriction
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
      (sixSymmetrization (restrictedComponentPower K s m)) := by sorry
