-- Prove2me | solution 1 for mme_ctensor_one_h_one_family_has_single_matrix_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T15:51:13.548984+00:00
-- url     : https://prove2.me/submissions/e6a70e55-d3a6-4ccc-8b76-90e50fdd7226

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_tensor_quotient

open MME MME.TensorObj PiTensorProduct

set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] {T : TensorObj K 3}
    {A H volume : ℕ}
    (family : CTensorOneHOneFamilyCertificate T A H volume)
    (hA : 0 < A) (hH : 0 < H) :
    ∃ a : Fin A, ∃ h : Fin H,
      TensorObj.Restrict
        (MMObj K ((family.certificate a).m h)
          ((family.certificate a).n h)
          ((family.certificate a).p h)) T ∧
      (family.certificate a).m h *
        (family.certificate a).n h *
        (family.certificate a).p h = volume := by
  classical
  let a : Fin A := ⟨0, hA⟩
  let h : Fin H := ⟨0, hH⟩
  let cert := family.certificate a
  refine ⟨a, h, ?_, cert.common_volume h⟩
  have hcomponent :
      TensorObj.Restrict
        (MMObj K (cert.m h) (cert.n h) (cert.p h))
        (cert.grading.blockSubtensor (cTensorOneHOneAddress H h)) :=
    (cert.component h).1
  have hblock :
      TensorObj.Restrict
        (cert.grading.blockSubtensor (cTensorOneHOneAddress H h))
        (family.star a) := by
    refine ⟨fun i => cert.grading.blockProj i (cTensorOneHOneAddress H h i), ?_⟩
    rfl
  have hstar : TensorObj.Restrict (family.star a) (TensorObj.bigAdd family.star) := by
    cases A with
    | zero => cases hA
    | succ n =>
      cases n with
      | zero =>
        simpa [a, TensorObj.bigAdd] using
          (TensorObj.Restrict.refl (family.star (0 : Fin 1)))
      | succ n =>
        refine ⟨fun i =>
          LinearMap.fst K ((family.star 0).V i)
            ((TensorObj.bigAdd (fun i => family.star i.succ)).V i), ?_⟩
        have hmap_zero :
            PiTensorProduct.map
              (fun i => (0 :
                ((TensorObj.bigAdd (fun i => family.star i.succ)).V i) →ₗ[K]
                  (family.star 0).V i)) = 0 := by
          apply PiTensorProduct.ext
          ext x
          simp only [LinearMap.compMultilinearMap_apply,
            PiTensorProduct.map_tprod, LinearMap.zero_apply]
          rw [PiTensorProduct.tprod_eq_tprodCoeff_one]
          exact PiTensorProduct.zero_tprodCoeff' (1 : K)
            (fun i => (0 : (family.star 0).V i)) (0 : Fin 3) rfl
        simp only [a, TensorObj.bigAdd, TensorObj.add]
        show PiTensorProduct.map
            (fun i => LinearMap.fst K ((family.star 0).V i)
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i))
            (PiTensorProduct.map
                (fun i => LinearMap.inl K ((family.star 0).V i)
                  ((TensorObj.bigAdd (fun i => family.star i.succ)).V i))
                (family.star 0).t +
             PiTensorProduct.map
                (fun i => LinearMap.inr K ((family.star 0).V i)
                  ((TensorObj.bigAdd (fun i => family.star i.succ)).V i))
                (TensorObj.bigAdd (fun i => family.star i.succ)).t) =
          (family.star ⟨0, hA⟩).t
        refine Eq.trans ((PiTensorProduct.map
          (fun i => LinearMap.fst K ((family.star 0).V i)
            ((TensorObj.bigAdd (fun i => family.star i.succ)).V i))).map_add _ _) ?_
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
        rw [show
          (fun i => LinearMap.fst K ((family.star 0).V i)
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i) ∘ₗ
            LinearMap.inl K ((family.star 0).V i)
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i)) =
            fun i =>
              (LinearMap.id : (family.star 0).V i →ₗ[K] (family.star 0).V i)
          from by funext i; ext x; rfl]
        rw [show
          (fun i => LinearMap.fst K ((family.star 0).V i)
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i) ∘ₗ
            LinearMap.inr K ((family.star 0).V i)
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i)) =
            fun i => (0 :
              ((TensorObj.bigAdd (fun i => family.star i.succ)).V i) →ₗ[K]
                (family.star 0).V i)
          from by funext i; ext x; rfl]
        rw [PiTensorProduct.map_id, hmap_zero]
        simp
  exact TensorObj.Restrict.trans
    (TensorObj.Restrict.trans
      (TensorObj.Restrict.trans hcomponent hblock)
      hstar)
    family.restrict
