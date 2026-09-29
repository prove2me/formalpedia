-- Prove2me | solution 1 for mme_Ctensor_three_unequal_word_induced_matching_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:33:19.949226+00:00
-- url     : https://prove2.me/submissions/c4de9767-f9b6-4754-938a-61d3bb8f15ec

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME TensorProduct PiTensorProduct BigOperators
open MME.TensorObj.TypeGrading

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.UnequalWordExtraction

variable {K : Type u} [Field K]
variable {X Y Z : TensorObj K 3} {t t0 t1 t2 : ℕ}

/-- Encode the three factor grades at one mode. -/
private def cyclicTripleGrade
    (rhoX : Fin 3 → Fin t0) (rhoY : Fin 3 → Fin t1)
    (rhoZ : Fin 3 → Fin t2) (i : Fin 3) :
    Fin (t0 * (t1 * t2)) :=
  finProdFinEquiv
    (rhoX i,
      finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))

private theorem blockTensor_ne_zero_congr
    {A : TensorObj K 3} (G : A.TypeGrading t)
    {rho sigma : Fin 3 → Fin t} (h : rho = sigma) :
    G.blockTensor rho ≠ 0 ↔ G.blockTensor sigma ≠ 0 := by
  subst sigma
  rfl

/-- Product grading on the heterogeneous cyclic product. -/
private noncomputable def threeCyclicTripleGrading
    (GX : X.TypeGrading t0) (GY : Y.TypeGrading t1)
    (GZ : Z.TypeGrading t2) :
    (threeStarCyclicProduct X Y Z).TypeGrading (t0 * (t1 * t2)) :=
  kronGrading GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))

private theorem threeCyclicTripleGrading_blockTensor_ne_zero_first
    (GX : X.TypeGrading t0) (GY : Y.TypeGrading t1)
    (GZ : Z.TypeGrading t2)
    (rhoX : Fin 3 → Fin t0) (rhoY : Fin 3 → Fin t1)
    (rhoZ : Fin 3 → Fin t2)
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

private theorem threeCyclicTripleGrading_blockTensor_ne_zero_second
    (GX : X.TypeGrading t0) (GY : Y.TypeGrading t1)
    (GZ : Z.TypeGrading t2)
    (rhoX : Fin 3 → Fin t0) (rhoY : Fin 3 → Fin t1)
    (rhoZ : Fin 3 → Fin t2)
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

private theorem threeCyclicTripleGrading_blockTensor_ne_zero_third
    (GX : X.TypeGrading t0) (GY : Y.TypeGrading t1)
    (GZ : Z.TypeGrading t2)
    (rhoX : Fin 3 → Fin t0) (rhoY : Fin 3 → Fin t1)
    (rhoZ : Fin 3 → Fin t2)
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
private theorem threeCyclicTripleGrading_blockSubtensor_iso
    (GX : X.TypeGrading t0) (GY : Y.TypeGrading t1)
    (GZ : Z.TypeGrading t2)
    (rhoX : Fin 3 → Fin t0) (rhoY : Fin 3 → Fin t1)
    (rhoZ : Fin 3 → Fin t2) :
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
  let sy : Fin 3 → Fin t1 := fun i ↦ rhoY (cyclicPerm.symm i)
  let sz : Fin 3 → Fin t2 := fun i ↦
    rhoZ ((cyclicPerm.trans cyclicPerm).symm i)
  have hinner := mme_TypeGrading_kron_blockSubtensor_iso GY' GZ' sy sz
  have hlift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (GX.blockSubtensor rhoX)) hinner
  have houter := mme_TypeGrading_kron_blockSubtensor_iso
    GX (kronGrading GY' GZ') rhoX
      (fun i ↦ finProdFinEquiv (sy i, sz i))
  exact hlift.trans houter

variable {H volume H0 H1 H2 v0 v1 v2 R W0 W1 W2 : ℕ}

private theorem ctensorOncePermutedComponentIso
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

private theorem ctensorTwicePermutedComponentIso
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
private theorem threeCTensorCyclicCoordinateBlockIso
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (x : Fin H0) (y : Fin H1) (z : Fin H2) :
    TensorObj.Isomorphic
      (MMObj K
        (certX.m x * certY.p y * certZ.n z)
        (certX.n x * certY.m y * certZ.p z)
        (certX.p x * certY.n y * certZ.m z))
      ((threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockSubtensor
        (cyclicTripleGrade
          (cTensorOneHOneAddress H0 x)
          (cTensorOneHOneAddress H1 y)
          (cTensorOneHOneAddress H2 z))) := by
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
    (cTensorOneHOneAddress H0 x)
    (cTensorOneHOneAddress H1 y)
    (cTensorOneHOneAddress H2 z)
  simpa only [mul_assoc] using hmm.symm.trans (hcomponents.trans hblock)

/-- The direct (one-position) address of a heterogeneous cyclic C-tensor
component. -/
private def threeCTensorDirectAddress
    (e : Fin H0 × Fin H1 × Fin H2) (i : Fin 3) (_r : Fin 1) :
    Fin ((H0 + 1) * ((H1 + 1) * (H2 + 1))) :=
  cyclicTripleGrade
    (cTensorOneHOneAddress H0 e.1)
    (cTensorOneHOneAddress H1 e.2.1)
    (cTensorOneHOneAddress H2 e.2.2) i

/-- Nonzero mixed direct blocks force exactly the three collisions used by
an induced matching in matrix-multiplication support. -/
private theorem threeCTensorDirectAddress_mixed_support
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (es : Fin 3 → (Fin H0 × Fin H1 × Fin H2))
    (hsupp :
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockTensor
        (fun i ↦ threeCTensorDirectAddress (es i) i 0) ≠ 0) :
    (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1 := by
  let rhoX : Fin 3 → Fin (H0 + 1) := fun j ↦
    cTensorOneHOneAddress H0 (es j).1 j
  let rhoY : Fin 3 → Fin (H1 + 1) := fun j ↦
    cTensorOneHOneAddress H1 (es (cyclicPerm j)).2.1 j
  let rhoZ : Fin 3 → Fin (H2 + 1) := fun j ↦
    cTensorOneHOneAddress H2
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
      Finset.univ.image (cTensorOneHOneAddress H0) := by
    by_contra hn
    exact hx (certX.supported rhoX hn)
  have hymem : rhoY ∈
      Finset.univ.image (cTensorOneHOneAddress H1) := by
    by_contra hn
    exact hy (certY.supported rhoY hn)
  have hzmem : rhoZ ∈
      Finset.univ.image (cTensorOneHOneAddress H2) := by
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
    apply Fin.castSucc_injective H0
    simpa [rhoX, cTensorOneHOneAddress] using hx0
  have hx1' : xh = (es 1).1 := by
    apply Fin.castSucc_injective H0
    simpa [rhoX, cTensorOneHOneAddress] using hx1
  have hy0' : yh = (es 1).2.1 := by
    apply Fin.castSucc_injective H1
    simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using hy0
  have hy1' : yh = (es 2).2.1 := by
    apply Fin.castSucc_injective H1
    simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using hy1
  have hz0' : zh = (es 2).2.2 := by
    apply Fin.castSucc_injective H2
    simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using hz0
  have hz1' : zh = (es 0).2.2 := by
    apply Fin.castSucc_injective H2
    simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using hz1
  exact ⟨hy0'.symm.trans hy1', hz0'.symm.trans hz1',
    hx0'.symm.trans hx1'⟩


private def wordAddress
    (w0 : Fin W0 → Fin R → Fin H0)
    (w1 : Fin W1 → Fin R → Fin H1)
    (w2 : Fin W2 → Fin R → Fin H2)
    (e : Fin W0 × Fin W1 × Fin W2) (i : Fin 3) (r : Fin R) :
    Fin ((H0 + 1) * ((H1 + 1) * (H2 + 1))) :=
  threeCTensorDirectAddress (w0 e.1 r, w1 e.2.1 r, w2 e.2.2 r) i 0

private theorem wordAddress_mixed_support
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (w0 : Fin W0 → Fin R → Fin H0) (hw0 : Function.Injective w0)
    (w1 : Fin W1 → Fin R → Fin H1) (hw1 : Function.Injective w1)
    (w2 : Fin W2 → Fin R → Fin H2) (hw2 : Function.Injective w2)
    (es : Fin 3 → (Fin W0 × Fin W1 × Fin W2))
    (hsupp : ∀ r : Fin R,
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockTensor
        (fun i ↦ wordAddress w0 w1 w2 (es i) i r) ≠ 0) :
    (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1 := by
  have hpoint (r : Fin R) := threeCTensorDirectAddress_mixed_support
    certX certY certZ
    (fun i ↦ (w0 (es i).1 r, w1 (es i).2.1 r, w2 (es i).2.2 r))
    (hsupp r)
  refine ⟨hw1 (funext fun r ↦ (hpoint r).1),
    hw2 (funext fun r ↦ (hpoint r).2.1),
    hw0 (funext fun r ↦ (hpoint r).2.2)⟩

private theorem wordAddress_component_iso
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (w0 : Fin W0 → Fin R → Fin H0)
    (w1 : Fin W1 → Fin R → Fin H1)
    (w2 : Fin W2 → Fin R → Fin H2)
    (e : Fin W0 × Fin W1 × Fin W2) :
    TensorObj.Isomorphic
      (MMObj K
        (∏ r, certX.m (w0 e.1 r) * certY.p (w1 e.2.1 r) * certZ.n (w2 e.2.2 r))
        (∏ r, certX.n (w0 e.1 r) * certY.m (w1 e.2.1 r) * certZ.p (w2 e.2.2 r))
        (∏ r, certX.p (w0 e.1 r) * certY.n (w1 e.2.1 r) * certZ.m (w2 e.2.2 r)))
      (gradedAddressBlock
        (threeCyclicTripleGrading certX.grading certY.grading certZ.grading)
        (wordAddress w0 w1 w2 e)) := by
  let a : Fin R → ℕ := fun r ↦
    certX.m (w0 e.1 r) * certY.p (w1 e.2.1 r) * certZ.n (w2 e.2.2 r)
  let b : Fin R → ℕ := fun r ↦
    certX.n (w0 e.1 r) * certY.m (w1 e.2.1 r) * certZ.p (w2 e.2.2 r)
  let c : Fin R → ℕ := fun r ↦
    certX.p (w0 e.1 r) * certY.n (w1 e.2.1 r) * certZ.m (w2 e.2.2 r)
  have hpoint : ∀ r : Fin R, TensorObj.Isomorphic
      (MMObj K (a r) (b r) (c r))
      ((threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockSubtensor
        (fun i ↦ wordAddress w0 w1 w2 e i r)) := by
    intro r
    exact threeCTensorCyclicCoordinateBlockIso certX certY certZ
      (w0 e.1 r) (w1 e.2.1 r) (w2 e.2.2 r)
  have htransport := mme_kronFin_respects_iso R
    (fun r ↦ MMObj K (a r) (b r) (c r))
    (fun r ↦ (threeCyclicTripleGrading
      certX.grading certY.grading certZ.grading).blockSubtensor
      (fun i ↦ wordAddress w0 w1 w2 e i r)) hpoint
  have hmm := mme_kronFin_MMObj_iso (K := K) R a b c
  exact hmm.symm.trans htransport

private theorem wordAddress_common_volume
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (w0 : Fin W0 → Fin R → Fin H0)
    (w1 : Fin W1 → Fin R → Fin H1)
    (w2 : Fin W2 → Fin R → Fin H2)
    (e : Fin W0 × Fin W1 × Fin W2) :
    (∏ r, certX.m (w0 e.1 r) * certY.p (w1 e.2.1 r) * certZ.n (w2 e.2.2 r)) *
      (∏ r, certX.n (w0 e.1 r) * certY.m (w1 e.2.1 r) * certZ.p (w2 e.2.2 r)) *
      (∏ r, certX.p (w0 e.1 r) * certY.n (w1 e.2.1 r) * certZ.m (w2 e.2.2 r)) =
      (v0 * v1 * v2) ^ R := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ _r : Fin R, (v0 * v1 * v2) := by
      apply Finset.prod_congr rfl
      intro r _
      calc
        _ = (certX.m (w0 e.1 r) * certX.n (w0 e.1 r) * certX.p (w0 e.1 r)) *
            (certY.m (w1 e.2.1 r) * certY.n (w1 e.2.1 r) * certY.p (w1 e.2.1 r)) *
            (certZ.m (w2 e.2.2 r) * certZ.n (w2 e.2.2 r) * certZ.p (w2 e.2.2 r)) := by
              ac_rfl
        _ = v0 * v1 * v2 := by rw [certX.common_volume, certY.common_volume, certZ.common_volume]
    _ = (v0 * v1 * v2) ^ R := by simp

end MME.UnequalWordExtraction

open MME.UnequalWordExtraction in
theorem solution
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 R W0 W1 W2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (w0 : Fin W0 → Fin R → Fin H0) (hw0 : Function.Injective w0)
    (w1 : Fin W1 → Fin R → Fin H1) (hw1 : Function.Injective w1)
    (w2 : Fin W2 → Fin R → Fin H2) (hw2 : Function.Injective w2)
    (E : Finset (Fin W0 × Fin W1 × Fin W2))
    (_hxy : Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)))
    (_hyz : Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)))
    (_hzx : Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)))
    (hinduced : ∀ x y z : E,
      x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 → z.1.1 = x.1.1 →
      x = y ∧ y = z) :
    ∃ a b c : Fin E.card → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      ∀ i, a i * b i * c i = (v0 * v1 * v2) ^ R := by
  classical
  let enum : Fin E.card ≃ E := E.equivFin.symm
  let edge : Fin E.card → (Fin W0 × Fin W1 × Fin W2) := fun j ↦ (enum j).1
  let G := threeCyclicTripleGrading certX.grading certY.grading certZ.grading
  let A : Fin E.card → Fin 3 → Fin R →
      Fin ((H0 + 1) * ((H1 + 1) * (H2 + 1))) :=
    fun j ↦ wordAddress w0 w1 w2 (edge j)
  have hInduced : ∀ js : Fin 3 → Fin E.card,
      (∀ r : Fin R, G.blockTensor (fun i ↦ A (js i) i r) ≠ 0) →
      ∃ j : Fin E.card, js = fun _ ↦ j := by
    intro js hnonzero
    let es : Fin 3 → (Fin W0 × Fin W1 × Fin W2) := fun i ↦ edge (js i)
    have hs := wordAddress_mixed_support certX certY certZ
      w0 hw0 w1 hw1 w2 hw2 es hnonzero
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
      ((threeStarCyclicProduct X Y Z).kronPow R) :=
    mme_induced_graded_address_blocks_restrict G A hInduced
  let a : Fin E.card → ℕ := fun j ↦
    ∏ r, certX.m (w0 (edge j).1 r) * certY.p (w1 (edge j).2.1 r) * certZ.n (w2 (edge j).2.2 r)
  let b : Fin E.card → ℕ := fun j ↦
    ∏ r, certX.n (w0 (edge j).1 r) * certY.m (w1 (edge j).2.1 r) * certZ.p (w2 (edge j).2.2 r)
  let c : Fin E.card → ℕ := fun j ↦
    ∏ r, certX.p (w0 (edge j).1 r) * certY.n (w1 (edge j).2.1 r) * certZ.m (w2 (edge j).2.2 r)
  have hmm : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (A j))) := by
    apply mme_bigAdd_mono_restrict
    intro j
    exact (wordAddress_component_iso certX certY certZ w0 w1 w2 (edge j)).1
  refine ⟨a, b, c, TensorObj.Restrict.trans hmm hblocks, ?_⟩
  intro j
  exact wordAddress_common_volume certX certY certZ w0 w1 w2 (edge j)
