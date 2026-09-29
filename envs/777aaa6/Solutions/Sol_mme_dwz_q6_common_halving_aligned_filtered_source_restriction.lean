-- Prove2me | solution 1 for mme_dwz_q6_common_halving_aligned_filtered_source_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:36:47.611476+00:00
-- url     : https://prove2.me/submissions/cfbf3967-a1b8-4cc3-a571-a0485688ff2b

import Theorems.Thm_mme_kron_power_position_permutation_basis_transport
import Theorems.Thm_mme_dwz_q6_common_halving_joined_filtered_source_restriction

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

private def coupledIndex : Fin 3 → Type u
  | ⟨0, _⟩ => ULift.{u} (Fin 6 ⊕ Fin 6)
  | ⟨1, _⟩ => ULift.{u} (Fin 6 ⊕ Fin 6)
  | ⟨2, _⟩ => ULift.{u} (Fin 2 ⊕ Fin 6 × Fin 6)

private noncomputable def coupledBasis {K : Type u} [Field K] :
    (i : Fin 3) → Basis (coupledIndex i) K ((coupledObj K 6).V i)
  | ⟨0, _⟩ => (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
  | ⟨1, _⟩ => (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
  | ⟨2, _⟩ => (Pi.basisFun K (Fin 2 ⊕ Fin 6 × Fin 6)).reindex Equiv.ulift.symm

private theorem mask_commute {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {α : Type u} (b : Basis α K V) (F : V ≃ₗ[K] V) (e : Equiv.Perm α)
    (hb : ∀ a, F (b a) = b (e a))
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ a, q (e a) ↔ p a) :
    F.toLinearMap.comp (b.constr K (fun a => if p a then b a else 0)) =
      (b.constr K (fun a => if q a then b a else 0)).comp F.toLinearMap := by
  apply b.ext
  intro a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Basis.constr_basis, hb, Basis.constr_basis]
  simp only [hp]
  split_ifs
  · exact hb a
  · exact F.map_zero

/-- The actual DWZ source restricts to a single coupled power with the family's
first-half X and second-half Y filters on their original family positions. -/
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
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  intro T b bX bY grade keepX keepY f
  letI : DecidablePred keepX := Classical.decPred _
  letI : DecidablePred keepY := Classical.decPred _
  let e : Equiv.Perm (Fin (N + N)) :=
    finSumFinEquiv.symm.trans (halving.position.trans (finCongr (by omega)))
  have hleft (r : Fin N) : e ⟨r.val, by omega⟩ =
      ⟨(halving.position (Sum.inl r)).val, by omega⟩ := by
    have hr : (⟨r.val, by omega⟩ : Fin (N + N)) = finSumFinEquiv (Sum.inl r) := rfl
    rw [hr]
    change (finCongr (show 2 * N = N + N by omega)) (halving.position
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl r)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hright (r : Fin N) : e ⟨N + r.val, by omega⟩ =
      ⟨(halving.position (Sum.inr r)).val, by omega⟩ := by
    have hr : (⟨N + r.val, by omega⟩ : Fin (N + N)) = finSumFinEquiv (Sum.inr r) := rfl
    rw [hr]
    change (finCongr (show 2 * N = N + N by omega)) (halving.position
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr r)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  let srcX := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N) =>
    ∃ p : Fin A × Fin H, ∀ r : Fin N,
      grade (PowIndex.get (N + N) w ⟨r.val, by omega⟩) =
        (family.entry p).val 0 (halving.position (Sum.inl r))
  let srcY := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N) =>
    ∃ p : Fin A × Fin H, ∀ r : Fin N,
      grade (PowIndex.get (N + N) w ⟨N + r.val, by omega⟩) =
        (family.entry p).val 1 (halving.position (Sum.inr r))
  letI : DecidablePred srcX := Classical.decPred _
  letI : DecidablePred srcY := Classical.decPred _
  let g : ∀ i, T.V i →ₗ[K] T.V i := Function.update
    (Function.update (fun _ => LinearMap.id) 0
      (bX.constr K (fun w => if srcX w then bX w else 0))) 1
    (bY.constr K (fun w => if srcY w then bY w else 0))
  obtain ⟨F, hF, hb⟩ := mme_kron_power_position_permutation_basis_transport
    (coupledObj K 6) coupledBasis (N + N) e
  obtain ⟨permX, hbX, hgetX⟩ := hb 0
  obtain ⟨permY, hbY, hgetY⟩ := hb 1
  have hx (w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N)) :
      keepX (permX w) ↔ srcX w := by
    have hread (r : Fin N) : PowIndex.get (N + N) (permX w)
        ⟨(halving.position (Sum.inl r)).val, by omega⟩ =
          PowIndex.get (N + N) w ⟨r.val, by omega⟩ := by
      rw [hgetX, ← hleft, e.symm_apply_apply]
      rfl
    change (∃ p : Fin A × Fin H, ∀ r : Fin N,
      grade (PowIndex.get (N + N) (permX w) ⟨(halving.position (Sum.inl r)).val, by omega⟩) =
        (family.entry p).val 0 (halving.position (Sum.inl r))) ↔ _
    apply exists_congr
    intro p
    apply forall_congr'
    intro r
    erw [hread r]
  have hy (w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (N + N)) :
      keepY (permY w) ↔ srcY w := by
    have hread (r : Fin N) : PowIndex.get (N + N) (permY w)
        ⟨(halving.position (Sum.inr r)).val, by omega⟩ =
          PowIndex.get (N + N) w ⟨N + r.val, by omega⟩ := by
      rw [hgetY, ← hright, e.symm_apply_apply]
      rfl
    change (∃ p : Fin A × Fin H, ∀ r : Fin N,
      grade (PowIndex.get (N + N) (permY w) ⟨(halving.position (Sum.inr r)).val, by omega⟩) =
        (family.entry p).val 1 (halving.position (Sum.inr r))) ↔ _
    apply exists_congr
    intro p
    apply forall_congr'
    intro r
    erw [hread r]
  have hcomp : (fun i => (F i).toLinearMap.comp (g i)) =
      fun i => (f i).comp (F i).toLinearMap := by
    funext i
    fin_cases i
    · exact mask_commute bX (F 0) permX hbX srcX keepX hx
    · exact mask_commute bY (F 1) permY hbY srcY keepY hy
    · rfl
  have ht : TensorObj.Restrict { T with t := PiTensorProduct.map f T.t }
      { T with t := PiTensorProduct.map g T.t } := by
    refine ⟨fun i => (F i).toLinearMap, ?_⟩
    change (PiTensorProduct.map (fun i => (F i).toLinearMap) ∘ₗ
      PiTensorProduct.map g) T.t = PiTensorProduct.map f T.t
    rw [← PiTensorProduct.map_comp, hcomp, PiTensorProduct.map_comp,
      LinearMap.comp_apply, hF]
  exact (mme_cyclicSymmetrization_mono_restrict ht).trans
    (mme_dwz_q6_common_halving_joined_filtered_source_restriction
      (K := K) s hs m hN family halving)

#print axioms solution
