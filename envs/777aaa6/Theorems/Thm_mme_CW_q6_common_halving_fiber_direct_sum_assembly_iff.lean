-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_fiber_direct_sum_assembly_iff
-- name    : mme_CW_q6_common_halving_fiber_direct_sum_assembly_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:41:09.779315+00:00
-- url     : https://prove2.me/theorems/d52ee6da-60cc-484d-b1b3-52eec048f4f5
-- title:
--   Exact half-pattern criterion for literal within-color direct-sum assembly
-- statement:
--   Let $K$ be a field and let a primary coupled-address family admit a common balanced halving into two sets of $N$ positions. Fix one color with $H$ entries. Write $T$ for the paired oriented coupled source, $B_h$ for its component at entry $h$, and $P_{h,i}$ for the corresponding component projection in physical mode $i$. Let $X_L(h)$ and $Y_R(h)$ denote the first-half X and second-half Y grade words. Then
--   $$\left(\bigotimes_{i=0}^2\sum_{h=0}^{H-1}\iota_{h,i}P_{h,i}\right)T
--   =\bigoplus_{h=0}^{H-1}B_h
--   \quad\Longleftrightarrow\quad X_L\text{ and }Y_R\text{ are both injective},$$
--   where $\iota_{h,i}$ is the inclusion of the $h$th summand. Thus half-pattern collisions obstruct this literal direct-sum assembly over every field. This criterion does not rule out different restriction maps or a C-tensor packing that retains mixed terms.
-- source:
--   Multilinear expansion and direct-sum coordinate projections; in the coupled-family application, the accepted exact mixed-projection support theorem and within-color half-pattern support criterion.

import Theorems.Thm_mme_direct_sum_component_assembly_iff_mixed_vanishing
import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
import Theorems.Thm_mme_CW_q6_common_halving_fiber_paired_induced_iff

open MME MME.PairedOrientedPackaging PiTensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_CW_q6_common_halving_fiber_direct_sum_assembly_iff
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    let T := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    let B := fun h : Fin H => componentObj (K := K) family halving (a,h)
    PiTensorProduct.map (fun i => ∑ h : Fin H,
      (gradedBigAddSlot H B h i).comp (componentProj family halving (a,h) i)) T.t =
        (TensorObj.bigAdd B).t ↔
      Function.Injective (fun h : Fin H => fun r : Fin N =>
        (family.entry (a,h)).val 0 (halving.position (Sum.inl r))) ∧
      Function.Injective (fun h : Fin H => fun r : Fin N =>
        (family.entry (a,h)).val 1 (halving.position (Sum.inr r))) := by sorry
