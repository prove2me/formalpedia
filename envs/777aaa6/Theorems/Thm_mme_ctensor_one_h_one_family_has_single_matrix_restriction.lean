-- Prove2me | Theorems.Thm_mme_ctensor_one_h_one_family_has_single_matrix_restriction
-- name    : mme_ctensor_one_h_one_family_has_single_matrix_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T14:41:45.611151+00:00
-- url     : https://prove2.me/theorems/cac9a94e-91a8-4acc-af4e-b384983a336d
-- title:
--   One actual matrix restriction from a finite C-tensor family
-- statement:
--   If a finite outer family of C-tensors has at least one outer member and each member has at least one component, then one component matrix-multiplication tensor is an actual restriction of the original source. The selected component retains the common volume recorded by the certificate.
-- source:
--   This is the one-component restriction consequence of the exact CTensorOneHOneFamilyCertificate and CTensorOneHOneCertificate fields (Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, 1990, p. 271). It supplies the actual Restrict field required by Stage.ChildMM in the More Asymmetry v2 Section 6 recursive construction; the existing Behrend extraction theorem only supplies a large direct sum inside cyclicSymmetrization.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_tensor_quotient

open MME MME.TensorObj

universe u
set_option autoImplicit false

theorem mme_ctensor_one_h_one_family_has_single_matrix_restriction {K : Type u} [Field K] {T : TensorObj K 3}
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
        (family.certificate a).p h = volume := by sorry
