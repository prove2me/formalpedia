-- Prove2me | Theorems.Thm_mme_induced_mode_choice_certificate_precompose_restrict
-- name    : mme_induced_mode_choice_certificate_precompose_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:24:21.747338+00:00
-- url     : https://prove2.me/theorems/67eb71b3-89d5-4a7d-a0db-99bde5066fb4
-- title:
--   Induced mode-choice certificates precompose along source restrictions
-- statement:
--   Suppose a tensor called middle is a restriction of a source tensor, and middle carries a finite induced mode-choice certificate realizing a target tensor. Then the source carries a certificate realizing the same target. Each certificate mode map is precomposed with the corresponding restriction map; the retained choices, off-support vanishing, and target sum are preserved.
-- source:
--   Standard functoriality of multilinear tensor maps; used in the laser-method source-projection step of Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5--6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_tensor_quotient

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false

theorem mme_induced_mode_choice_certificate_precompose_restrict
    {K : Type u} [Field K]
    {source middle target : TensorObj K 3}
    (hMiddle : TensorObj.Restrict middle source)
    (hCert : Nonempty (InducedModeChoiceCertificate middle target)) :
    Nonempty (InducedModeChoiceCertificate source target) := by
  sorry
