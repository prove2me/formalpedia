-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_joined_filtered_source_restriction
-- name    : mme_dwz_q6_common_halving_joined_filtered_source_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:24:54.611209+00:00
-- url     : https://prove2.me/theorems/3deba517-e3c0-4f21-9ec6-c075e16717a7
-- title:
--   The DWZ source retains one coupled power with prefix and suffix filters
-- statement:
--   Fix row $s\in\{13,14\}$ of the DWZ component table, let $N=c_s m$, and let a primary coupled-address family with parameters $(N,L,G,A,H)$ admit a common balanced halving. Set $C=C_6$. In $C^{\otimes 2N}$, filter mode 0 by retaining numeric words whose first $N$ binary grades equal a first-half X word of some family entry. Filter mode 1 by retaining words whose last $N$ grades equal a second-half Y word of some family entry. The half words are read using the family's specified halving. Let $Z$ be the resulting tensor. Then
--   $$\operatorname{cyc}(Z)\preceq\operatorname{six}(R_{s,m}),$$
--   where $R_{s,m}$ is the restricted DWZ component power. All numeric coordinates with allowed grades are retained. This combines the two unpermuted filtered coupled powers into a single power; the prefix and suffix positions still need to be aligned with the original family positions for the subsequent family extraction.
-- source:
--   Coordinate-preserving concatenation of tensor powers and the common-halving unpermuted source restriction.

import Theorems.Thm_mme_kron_power_prefix_suffix_filter_restriction
import Theorems.Thm_mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_joined_filtered_source_restriction
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
        grade (PowIndex.get (N + N) w ⟨r.val, by omega⟩) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N) =>
      ∃ p : Fin A × Fin H, ∀ r : Fin N,
        grade (PowIndex.get (N + N) w ⟨N + r.val, by omega⟩) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    let f : ∀ i, T.V i →ₗ[K] T.V i := Function.update
      (Function.update (fun _ => LinearMap.id) 0
        (bX.constr K (fun w => if keepX w then bX w else 0))) 1
      (bY.constr K (fun w => if keepY w then bY w else 0))
    TensorObj.Restrict (cyclicSymmetrization { T with t := PiTensorProduct.map f T.t })
      (sixSymmetrization (restrictedComponentPower K s m)) := by sorry
