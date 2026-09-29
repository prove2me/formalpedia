-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction
-- name    : mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:13:24.399161+00:00
-- url     : https://prove2.me/theorems/df9db834-31d5-4d9a-98fa-68caf457472a
-- title:
--   The symmetrized DWZ source retains two unpermuted filtered coupled powers
-- statement:
--   Fix row $s\in\{13,14\}$ of the DWZ component table and let $N=c_s m$. Let a primary coupled-address family with parameters $(N,L,G,A,H)$ admit a common balanced halving. Set $C=C_6$. In the first copy of $C^{\otimes N}$, retain the mode-0 numeric words whose binary grades occur as a first-half X word of some family entry; call the resulting tensor $X$. In the second copy retain the mode-1 words whose grades occur as a second-half Y word; call this tensor $Y$. Then
--   $$\operatorname{cyc}(X\otimes Y)\preceq\operatorname{six}(R_{s,m}),$$
--   where $R_{s,m}$ is the restricted DWZ component power and $\preceq$ denotes tensor restriction. Both powers are in the original coupled orientation and retain all numeric coordinates on the allowed words. This supplies an unpermuted filtered source for the subsequent family extraction.
-- source:
--   Basis-preserving cyclic transport of the coupled tensor, word-basis transport to powers, and the common-halving reoriented source restriction.

import Theorems.Thm_mme_coupled_left_half_filtered_power_restriction
import Theorems.Thm_mme_coupled_right_half_filtered_power_restriction
import Theorems.Thm_mme_dwz_q6_common_halving_reoriented_half_cyclic_restriction
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let T := (coupledObj K 6).kronPow N
    let b := (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
    let bX := kronPowModeBasis (coupledObj K 6) 0 b N
    let bY := kronPowModeBasis (coupledObj K 6) 1 b N
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
    let f : ∀ i, T.V i →ₗ[K] T.V i := Function.update (fun _ => LinearMap.id) 0
      (bX.constr K (fun w => if keepX w then bX w else 0))
    let g : ∀ i, T.V i →ₗ[K] T.V i := Function.update (fun _ => LinearMap.id) 1
      (bY.constr K (fun w => if keepY w then bY w else 0))
    let X : TensorObj K 3 := { T with t := PiTensorProduct.map f T.t }
    let Y : TensorObj K 3 := { T with t := PiTensorProduct.map g T.t }
    TensorObj.Restrict (cyclicSymmetrization (TensorObj.kron X Y))
      (sixSymmetrization (restrictedComponentPower K s m)) := by sorry
