-- Prove2me | solution 1 for mme_dwz_q6_common_halving_joined_filtered_source_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:25:14.693988+00:00
-- url     : https://prove2.me/submissions/90ea7ff7-573d-421b-9767-80e783fa3543

import Theorems.Thm_mme_kron_power_prefix_suffix_filter_restriction
import Theorems.Thm_mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

/-- The actual DWZ source restricts to a single coupled power with the family's
first-half X and second-half Y filters on its prefix and suffix coordinates. -/
theorem solution
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
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  intro T b bX bY grade keepX keepY f
  let P := fun w : Fin N → ULift.{u} (Fin 6 ⊕ Fin 6) =>
    ∃ p : Fin A × Fin H, ∀ r,
      grade (w r) = (family.entry p).val 0 (halving.position (Sum.inl r))
  let Q := fun w : Fin N → ULift.{u} (Fin 6 ⊕ Fin 6) =>
    ∃ p : Fin A × Fin H, ∀ r,
      grade (w r) = (family.entry p).val 1 (halving.position (Sum.inr r))
  letI : DecidablePred P := Classical.decPred _
  letI : DecidablePred Q := Classical.decPred _
  have hj := mme_kron_power_prefix_suffix_filter_restriction (coupledObj K 6) N N b b P Q
  have hsour := mme_dwz_q6_common_halving_unpermuted_filtered_source_restriction
    (K := K) s hs m hN family halving
  exact (mme_cyclicSymmetrization_mono_restrict hj).trans hsour

#print axioms solution
