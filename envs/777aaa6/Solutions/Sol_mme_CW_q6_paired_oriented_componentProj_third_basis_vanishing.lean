-- Prove2me | solution 1 for mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:57:16.735413+00:00
-- url     : https://prove2.me/submissions/5e7b3e0f-06f8-482d-9449-e65b68177c8f

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

namespace MME.PairedProjectionWordVanishing

private theorem blockProj_apply_mem_ne
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (i : Fin 3) (a b : Fin t) (hab : a ≠ b)
    (x : T.V i) (hx : x ∈ G.decomp i b) : G.blockProj i a x = 0 := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

/-- A mismatch in one coordinate kills the projection of the entire basis word. -/
private theorem addressProj_basis_zero_of_mismatch
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (i : Fin 3) {ι : Type u}
    (basis : Basis ι K (T.V i)) (grade : ι → Fin t)
    (hgrade : ∀ x, basis x ∈ G.decomp i (grade x))
    (a : Fin 3 → Fin N → Fin t) (w : PowIndex ι N)
    (hbad : ∃ r, grade (PowIndex.get N w r) ≠ a i r) :
    gradedAddressProj G N a i (kronPowModeBasis T i basis N w) = 0 := by
  induction N with
  | zero => obtain ⟨r, _⟩ := hbad; exact r.elim0
  | succ N ih =>
    obtain ⟨r, hr⟩ := hbad
    change TensorProduct.map (G.blockProj i (a i 0))
        (gradedAddressProj G N (fun s j => a s j.succ) i)
        ((basis.tensorProduct (kronPowModeBasis T i basis N)) (w.1, w.2)) = 0
    rw [Basis.tensorProduct_apply, TensorProduct.map_tmul]
    refine Fin.cases (motive := fun r =>
      grade (PowIndex.get (N + 1) w r) ≠ a i r → _) ?_ (fun r' => ?_) r hr
    · intro h
      rw [blockProj_apply_mem_ne G i _ _ h.symm _ (hgrade w.1)]
      exact zero_tmul _ _
    · intro h
      rw [ih (fun s j => a s j.succ) w.2 ⟨r', h⟩]
      exact tmul_zero _ _

private theorem left_basis_mem (K : Type u) [Field K]
    (x : ULift.{u} (Fin 6 ⊕ Fin 6)) :
    ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) x ∈
      (leftGrading (K := K)).decomp 2
        (Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down) := by
  rw [Basis.reindex_apply]
  change (Pi.basisFun K (Fin 6 ⊕ Fin 6)) x.down ∈
    cwBasisGrade (dwzQ6CoupledBasis K 0) (dwzQ6CoupledCoordGrade 0)
      (Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down)
  apply Submodule.subset_span
  refine ⟨x.down, ?_, rfl⟩
  cases x with | up x => cases x <;> rfl

private theorem right_basis_mem (K : Type u) [Field K]
    (x : ULift.{u} (Fin 6 ⊕ Fin 6)) :
    ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) x ∈
      (rightGrading (K := K)).decomp 2
        (Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down) := by
  rw [Basis.reindex_apply]
  change (Pi.basisFun K (Fin 6 ⊕ Fin 6)) x.down ∈
    cwBasisGrade (dwzQ6CoupledBasis K 1) (dwzQ6CoupledCoordGrade 1)
      (Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down)
  apply Submodule.subset_span
  refine ⟨x.down, ?_, rfl⟩
  cases x with | up x => cases x <;> rfl

end MME.PairedProjectionWordVanishing

/-- The paired component map kills every third-mode basis word that disagrees
with either selected half-address. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (p : Fin A × Fin H)
    (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N) :
    let labelGrade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x => Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down
    ((∃ r, labelGrade (PowIndex.get N wX r) ≠
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∨
      (∃ r, labelGrade (PowIndex.get N wY r) ≠
        (family.entry p).val 1 (halving.position (Sum.inr r)))) →
    componentProj (K := K) family halving p 2
      (kronPowModeBasis
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wX ⊗ₜ[K]
        kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wY) = 0 := by
  intro labelGrade hbad
  unfold componentProj
  erw [TensorProduct.map_tmul]
  rcases hbad with hleft | hright
  · rw [MME.PairedProjectionWordVanishing.addressProj_basis_zero_of_mismatch
      (leftGrading (K := K)) 2 _ labelGrade
      (MME.PairedProjectionWordVanishing.left_basis_mem K)
      (leftAddress family halving p) wX hleft]
    exact zero_tmul _ _
  · rw [MME.PairedProjectionWordVanishing.addressProj_basis_zero_of_mismatch
      (rightGrading (K := K)) 2 _ labelGrade
      (MME.PairedProjectionWordVanishing.right_basis_mem K)
      (rightAddress family halving p) wY hright]
    exact tmul_zero _ _
