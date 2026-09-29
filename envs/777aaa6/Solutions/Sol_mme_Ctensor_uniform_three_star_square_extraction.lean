-- Prove2me | solution 1 for mme_Ctensor_uniform_three_star_square_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:12:59.277067+00:00
-- url     : https://prove2.me/submissions/5b51e5b2-2fa8-4aa8-88c8-f06adf39ecb8

import Definitions.Def_CTensorThreeCyclicBalancedGradingCertificate
import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_Ctensor_three_star_dimension_products_common_volume
import Theorems.Thm_mme_MM_support_behrend_induced_matching
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib.Tactic

open MME TensorProduct PiTensorProduct BigOperators
open MME.TensorObj.TypeGrading

universe u

namespace UniformThreeStarInternal

variable {K : Type u} [Field K]
variable {X Y Z : TensorObj K 3} {t : ℕ}

/-- Encode the three factor grades at one mode. -/
def cyclicTripleGrade
    (rhoX rhoY rhoZ : Fin 3 → Fin t) (i : Fin 3) :
    Fin (t * (t * t)) :=
  finProdFinEquiv
    (rhoX i,
      finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))

theorem blockTensor_ne_zero_congr
    {A : TensorObj K 3} (G : A.TypeGrading t)
    {rho sigma : Fin 3 → Fin t} (h : rho = sigma) :
    G.blockTensor rho ≠ 0 ↔ G.blockTensor sigma ≠ 0 := by
  subst sigma
  rfl

/-- Product grading on the heterogeneous cyclic product. -/
noncomputable def threeCyclicTripleGrading
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t) :
    (threeStarCyclicProduct X Y Z).TypeGrading (t * (t * t)) :=
  kronGrading GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))

theorem threeCyclicTripleGrading_blockTensor_ne_zero_first
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GX.blockTensor rhoX ≠ 0 := by
  exact kronGrading_blockTensor_ne_zero_left GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h

theorem threeCyclicTripleGrading_blockTensor_ne_zero_second
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GY.blockTensor rhoY ≠ 0 := by
  have hinner := kronGrading_blockTensor_ne_zero_right GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h
  have hperm := kronGrading_blockTensor_ne_zero_left
    (permObjGrading GY cyclicPerm)
    (permObjGrading GZ (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hy
  apply hperm
  rw [permObjGrading_blockTensor GY cyclicPerm rhoY, hy, map_zero]
  rfl

theorem threeCyclicTripleGrading_blockTensor_ne_zero_third
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GZ.blockTensor rhoZ ≠ 0 := by
  have hinner := kronGrading_blockTensor_ne_zero_right GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h
  have hperm := kronGrading_blockTensor_ne_zero_right
    (permObjGrading GY cyclicPerm)
    (permObjGrading GZ (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hz
  apply hperm
  rw [permObjGrading_blockTensor GZ
    (cyclicPerm.trans cyclicPerm) rhoZ, hz, map_zero]
  rfl

/-- One heterogeneous coordinate block is the nested Kronecker product of
the three corresponding factor blocks. -/
theorem threeCyclicTripleGrading_blockSubtensor_iso
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (GX.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading GY cyclicPerm).blockSubtensor
            (fun i ↦ rhoY (cyclicPerm.symm i)))
          ((permObjGrading GZ
              (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i ↦ rhoZ
              ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((threeCyclicTripleGrading GX GY GZ).blockSubtensor
        (cyclicTripleGrade rhoX rhoY rhoZ)) := by
  let GY' := permObjGrading GY cyclicPerm
  let GZ' := permObjGrading GZ (cyclicPerm.trans cyclicPerm)
  let sy : Fin 3 → Fin t := fun i ↦ rhoY (cyclicPerm.symm i)
  let sz : Fin 3 → Fin t := fun i ↦
    rhoZ ((cyclicPerm.trans cyclicPerm).symm i)
  have hinner := mme_TypeGrading_kron_blockSubtensor_iso GY' GZ' sy sz
  have hlift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (GX.blockSubtensor rhoX)) hinner
  have houter := mme_TypeGrading_kron_blockSubtensor_iso
    GX (kronGrading GY' GZ') rhoX
      (fun i ↦ finProdFinEquiv (sy i, sz i))
  exact hlift.trans houter

variable {H volume m W : ℕ}

theorem ctensorOncePermutedComponentIso
    {T : TensorObj K 3}
    (cert : CTensorOneHOneCertificate T H volume) (h : Fin H) :
    TensorObj.Isomorphic
      (MMObj K (cert.p h) (cert.m h) (cert.n h))
      ((permObjGrading cert.grading cyclicPerm).blockSubtensor
        (fun i ↦ (cTensorOneHOneAddress H h) (cyclicPerm.symm i))) := by
  have hmm := MME.MMObj_permObj_cyclic (K := K)
    (cert.m h) (cert.n h) (cert.p h)
  have hp := TensorObj.permObj_isomorphic cyclicPerm (cert.component h)
  have hg := permObjGrading_blockSubtensor_iso
    cert.grading cyclicPerm (cTensorOneHOneAddress H h)
  exact hmm.symm.trans (hp.trans hg.symm)

theorem ctensorTwicePermutedComponentIso
    {T : TensorObj K 3}
    (cert : CTensorOneHOneCertificate T H volume) (h : Fin H) :
    TensorObj.Isomorphic
      (MMObj K (cert.n h) (cert.p h) (cert.m h))
      ((permObjGrading cert.grading
          (cyclicPerm.trans cyclicPerm)).blockSubtensor
        (fun i ↦ (cTensorOneHOneAddress H h)
          ((cyclicPerm.trans cyclicPerm).symm i))) := by
  have hmm := mme_MMObj_permObj_cyclic_sq (K := K)
    (cert.m h) (cert.n h) (cert.p h)
  have hp := TensorObj.permObj_isomorphic
    (cyclicPerm.trans cyclicPerm) (cert.component h)
  have hg := permObjGrading_blockSubtensor_iso
    cert.grading (cyclicPerm.trans cyclicPerm)
      (cTensorOneHOneAddress H h)
  exact hmm.symm.trans (hp.trans hg.symm)

/-- The matrix-product shape of one coordinate block in a heterogeneous
cyclic product. -/
theorem threeCTensorCyclicCoordinateBlockIso
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (x y z : Fin H) :
    TensorObj.Isomorphic
      (MMObj K
        (certX.m x * certY.p y * certZ.n z)
        (certX.n x * certY.m y * certZ.p z)
        (certX.p x * certY.n y * certZ.m z))
      ((threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockSubtensor
        (cyclicTripleGrade
          (cTensorOneHOneAddress H x)
          (cTensorOneHOneAddress H y)
          (cTensorOneHOneAddress H z))) := by
  have hcomponents := TensorQ.mul_respects_iso (certX.component x)
    (TensorQ.mul_respects_iso
      (ctensorOncePermutedComponentIso certY y)
      (ctensorTwicePermutedComponentIso certZ z))
  have hinner := MMObj_kron_iso (K := K)
    (certY.p y) (certY.m y) (certY.n y)
    (certZ.n z) (certZ.p z) (certZ.m z)
  have hinnerLift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl
      (MMObj K (certX.m x) (certX.n x) (certX.p x))) hinner
  have houter := MMObj_kron_iso (K := K)
    (certX.m x) (certX.n x) (certX.p x)
    (certY.p y * certZ.n z)
    (certY.m y * certZ.p z)
    (certY.n y * certZ.m z)
  have hmm := hinnerLift.trans houter
  have hblock := threeCyclicTripleGrading_blockSubtensor_iso
    certX.grading certY.grading certZ.grading
    (cTensorOneHOneAddress H x)
    (cTensorOneHOneAddress H y)
    (cTensorOneHOneAddress H z)
  simpa only [mul_assoc] using hmm.symm.trans (hcomponents.trans hblock)

def threeCTensorDirectAddress
    (e : Fin H × Fin H × Fin H) (i : Fin 3) (_r : Fin 1) :
    Fin ((H + 1) * ((H + 1) * (H + 1))) :=
  cyclicTripleGrade
    (cTensorOneHOneAddress H e.1)
    (cTensorOneHOneAddress H e.2.1)
    (cTensorOneHOneAddress H e.2.2) i

/-- Nonzero mixed direct blocks force exactly the three collisions used by
an induced matching in matrix-multiplication support. -/
theorem threeCTensorDirectAddress_mixed_support
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (es : Fin 3 → (Fin H × Fin H × Fin H))
    (hsupp :
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockTensor
        (fun i ↦ threeCTensorDirectAddress (es i) i 0) ≠ 0) :
    (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1 := by
  let rhoX : Fin 3 → Fin (H + 1) := fun j ↦
    cTensorOneHOneAddress H (es j).1 j
  let rhoY : Fin 3 → Fin (H + 1) := fun j ↦
    cTensorOneHOneAddress H (es (cyclicPerm j)).2.1 j
  let rhoZ : Fin 3 → Fin (H + 1) := fun j ↦
    cTensorOneHOneAddress H
      (es ((cyclicPerm.trans cyclicPerm) j)).2.2 j
  have haddr :
      (fun i ↦ threeCTensorDirectAddress (es i) i 0) =
        cyclicTripleGrade rhoX rhoY rhoZ := by
    funext i
    simp only [threeCTensorDirectAddress, cyclicTripleGrade,
      rhoX, rhoY, rhoZ]
    rw [cyclicPerm.apply_symm_apply,
      (cyclicPerm.trans cyclicPerm).apply_symm_apply]
  have hblock :
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockTensor
        (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
    (blockTensor_ne_zero_congr
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading) haddr).mp hsupp
  have hx : certX.grading.blockTensor rhoX ≠ 0 :=
    threeCyclicTripleGrading_blockTensor_ne_zero_first
      certX.grading certY.grading certZ.grading rhoX rhoY rhoZ hblock
  have hy : certY.grading.blockTensor rhoY ≠ 0 :=
    threeCyclicTripleGrading_blockTensor_ne_zero_second
      certX.grading certY.grading certZ.grading rhoX rhoY rhoZ hblock
  have hz : certZ.grading.blockTensor rhoZ ≠ 0 :=
    threeCyclicTripleGrading_blockTensor_ne_zero_third
      certX.grading certY.grading certZ.grading rhoX rhoY rhoZ hblock
  have hxmem : rhoX ∈
      Finset.univ.image (cTensorOneHOneAddress H) := by
    by_contra hn
    exact hx (certX.supported rhoX hn)
  have hymem : rhoY ∈
      Finset.univ.image (cTensorOneHOneAddress H) := by
    by_contra hn
    exact hy (certY.supported rhoY hn)
  have hzmem : rhoZ ∈
      Finset.univ.image (cTensorOneHOneAddress H) := by
    by_contra hn
    exact hz (certZ.supported rhoZ hn)
  obtain ⟨xh, _, hxh⟩ := Finset.mem_image.mp hxmem
  obtain ⟨yh, _, hyh⟩ := Finset.mem_image.mp hymem
  obtain ⟨zh, _, hzh⟩ := Finset.mem_image.mp hzmem
  have hx0 := congrFun hxh 0
  have hx1 := congrFun hxh 1
  have hy0 := congrFun hyh 0
  have hy1 := congrFun hyh 1
  have hz0 := congrFun hzh 0
  have hz1 := congrFun hzh 1
  have hx0' : xh = (es 0).1 := by
    apply Fin.castSucc_injective H
    simpa [rhoX, cTensorOneHOneAddress] using hx0
  have hx1' : xh = (es 1).1 := by
    apply Fin.castSucc_injective H
    simpa [rhoX, cTensorOneHOneAddress] using hx1
  have hy0' : yh = (es 1).2.1 := by
    apply Fin.castSucc_injective H
    simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using hy0
  have hy1' : yh = (es 2).2.1 := by
    apply Fin.castSucc_injective H
    simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using hy1
  have hz0' : zh = (es 2).2.2 := by
    apply Fin.castSucc_injective H
    simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using hz0
  have hz1' : zh = (es 0).2.2 := by
    apply Fin.castSucc_injective H
    simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using hz1
  exact ⟨hy0'.symm.trans hy1', hz0'.symm.trans hz1',
    hx0'.symm.trans hx1'⟩

/-- A direct cyclic address is an MM block with the displayed heterogeneous
dimensions. -/
theorem threeCTensorDirectAddress_component_iso
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (e : Fin H × Fin H × Fin H) :
    TensorObj.Isomorphic
      (MMObj K
        (certX.m e.1 * certY.p e.2.1 * certZ.n e.2.2)
        (certX.n e.1 * certY.m e.2.1 * certZ.p e.2.2)
        (certX.p e.1 * certY.n e.2.1 * certZ.m e.2.2))
      (gradedAddressBlock
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading)
        (threeCTensorDirectAddress e)) := by
  let a : Fin 1 → ℕ := fun _ ↦
    certX.m e.1 * certY.p e.2.1 * certZ.n e.2.2
  let b : Fin 1 → ℕ := fun _ ↦
    certX.n e.1 * certY.m e.2.1 * certZ.p e.2.2
  let c : Fin 1 → ℕ := fun _ ↦
    certX.p e.1 * certY.n e.2.1 * certZ.m e.2.2
  have hpoint : ∀ r : Fin 1, TensorObj.Isomorphic
      (MMObj K (a r) (b r) (c r))
      ((threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockSubtensor
        (fun i ↦ threeCTensorDirectAddress e i r)) := by
    intro r
    exact threeCTensorCyclicCoordinateBlockIso certX certY certZ
      e.1 e.2.1 e.2.2
  have htransport := mme_kronFin_respects_iso 1
    (fun r ↦ MMObj K (a r) (b r) (c r))
    (fun r ↦ (threeCyclicTripleGrading
      certX.grading certY.grading certZ.grading).blockSubtensor
      (fun i ↦ threeCTensorDirectAddress e i r)) hpoint
  have hmm := mme_kronFin_MMObj_iso (K := K) 1 a b c
  simpa only [a, b, c, gradedAddressBlock, Fin.prod_univ_one]
    using hmm.symm.trans htransport


end UniformThreeStarInternal


open MME UniformThreeStarInternal BigOperators
set_option autoImplicit false

/-- Uniform leaf dimensions yield square matrix blocks in a cyclic triple. -/
theorem solution
    {K : Type u} [Field K] {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (m n p : ℕ)
    (hx : ∀ h, certX.m h = m ∧ certX.n h = n ∧ certX.p h = p)
    (hy : ∀ h, certY.m h = m ∧ certY.n h = n ∧ certY.p h = p)
    (hz : ∀ h, certZ.m h = m ∧ certZ.n h = n ∧ certZ.p h = p)
    (hH : 0 < H) :
    ∃ k : ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K (m * n * p) (m * n * p) (m * n * p)))
        (threeStarCyclicProduct X Y Z) ∧
      (H : ℝ) ^ 2 * Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (k : ℝ) := by
  classical
  obtain ⟨E, _, _, _, hinduced, hcard⟩ :=
    mme_MM_support_behrend_induced_matching H hH
  let enum : Fin E.card ≃ E := E.equivFin.symm
  let edge : Fin E.card → (Fin H × Fin H × Fin H) :=
    fun j ↦ (enum j).1
  let G := threeCyclicTripleGrading
    certX.grading certY.grading certZ.grading
  let A : Fin E.card → Fin 3 → Fin 1 →
      Fin ((H + 1) * ((H + 1) * (H + 1))) :=
    fun j ↦ threeCTensorDirectAddress (edge j)
  have hInduced : ∀ js : Fin 3 → Fin E.card,
      (∀ r : Fin 1,
        G.blockTensor (fun i ↦ A (js i) i r) ≠ 0) →
      ∃ j : Fin E.card, js = fun _ ↦ j := by
    intro js hnonzero
    let es : Fin 3 → (Fin H × Fin H × Fin H) :=
      fun i ↦ edge (js i)
    have hs := threeCTensorDirectAddress_mixed_support
      certX certY certZ es (by
        simpa only [G, A, es] using hnonzero 0)
    have hmixed := hinduced (enum (js 1)) (enum (js 2)) (enum (js 0))
      hs.1 hs.2.1 hs.2.2
    have h12 : js 1 = js 2 := enum.injective hmixed.1
    have h20 : js 2 = js 0 := enum.injective hmixed.2
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact h12.trans h20
    · exact h20
  have hblocks : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (A j)))
      ((threeStarCyclicProduct X Y Z).kronPow 1) :=
    mme_induced_graded_address_blocks_restrict G A hInduced
  have hmm : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.card ↦ MMObj K (m * n * p) (m * n * p) (m * n * p)))
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (A j))) := by
    apply mme_bigAdd_mono_restrict
    intro j
    have hi := (threeCTensorDirectAddress_component_iso certX certY certZ (edge j)).1
    simpa only [(hx _).1, (hx _).2.1, (hx _).2.2,
      (hy _).1, (hy _).2.1, (hy _).2.2,
      (hz _).1, (hz _).2.1, (hz _).2.2, mul_comm, mul_left_comm, mul_assoc] using hi
  have hone : TensorObj.Isomorphic ((threeStarCyclicProduct X Y Z).kronPow 1)
      (threeStarCyclicProduct X Y Z) := by
    apply (TensorQ.toQ_eq_iff).mp
    change TensorQ.toQ (TensorObj.kron (threeStarCyclicProduct X Y Z) TensorObj.oneObj) = _
    rw [← TensorQ.toQ_mul, ← TensorQ.toQ_one, mul_one]
  exact ⟨E.card, (hmm.trans hblocks).trans hone.1, hcard⟩


#print axioms solution
