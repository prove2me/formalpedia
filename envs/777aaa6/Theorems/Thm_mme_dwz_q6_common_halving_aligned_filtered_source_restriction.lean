-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_aligned_filtered_source_restriction
-- name    : mme_dwz_q6_common_halving_aligned_filtered_source_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:36:13.68426+00:00
-- url     : https://prove2.me/theorems/2f5f4317-abe7-4546-8a19-67ec3dc41dba
-- title:
--   Align the DWZ coupled-power filters with the family halving
-- statement:
--   Fix a DWZ row $s\in\{13,14\}$, $N=c_s m$, a primary coupled-address family with parameters $(N,L,G,A,H)$, and a common balanced halving. In $C_6^{\otimes 2N}$, retain mode-0 numeric words whose grades on the halving's first positions agree with the X grades of some family entry. In mode 1, retain words whose grades on the halving's second positions agree with the Y grades of some family entry. Mode 2 is unchanged. If $Z$ denotes this filtered tensor, then $\operatorname{cyc}(Z)\preceq\operatorname{six}(R_{s,m})$. These filters are on the original family positions, so the resulting source can be used with the family's original coordinate data. This is a source restriction, not yet the full family extraction or its volume estimate.
-- source:
--   Tensor-power position permutation and the accepted common-halving joined filtered source restriction.

import Theorems.Thm_mme_kron_power_position_permutation_basis_transport
import Theorems.Thm_mme_dwz_q6_common_halving_joined_filtered_source_restriction

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_aligned_filtered_source_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let T := (coupledObj K 6).kronPow (N + N)
    let b := (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
    let bX := kronPowModeBasis (coupledObj K 6) 0 b (N + N)
    let bY := kronPowModeBasis (coupledObj K 6) 1 b (N + N)
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x => Sum.elim (fun _ => 0) (fun _ => 1) x.down
    let keepX := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N) =>
      ∃ p : Fin A × Fin H, ∀ r : Fin N,
        grade (PowIndex.get (N + N) w ⟨(halving.position (Sum.inl r)).val, by omega⟩) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N) =>
      ∃ p : Fin A × Fin H, ∀ r : Fin N,
        grade (PowIndex.get (N + N) w ⟨(halving.position (Sum.inr r)).val, by omega⟩) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    let f : ∀ i, T.V i →ₗ[K] T.V i := Function.update
      (Function.update (fun _ => LinearMap.id) 0
        (bX.constr K (fun w => if keepX w then bX w else 0))) 1
      (bY.constr K (fun w => if keepY w then bY w else 0))
    TensorObj.Restrict (cyclicSymmetrization { T with t := PiTensorProduct.map f T.t })
      (sixSymmetrization (restrictedComponentPower K s m)) := by sorry
