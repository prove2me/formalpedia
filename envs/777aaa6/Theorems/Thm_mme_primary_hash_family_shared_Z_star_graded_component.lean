-- Prove2me | Theorems.Thm_mme_primary_hash_family_shared_Z_star_graded_component
-- name    : mme_primary_hash_family_shared_Z_star_graded_component
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:54:42.589336+00:00
-- url     : https://prove2.me/theorems/6a2356ce-0f1d-45b3-b8cd-7bdf664dd8d8
-- title:
--   Shared-Z star graded blocks recover address components
-- statement:
--   Let $T$ be a tensor over a field $K$ with a three-way grading, and let $\mathcal F$ be a primary coupled-address family with parameters $(N,L,G,A,H)$. Write $C_{a,h}$ for its address component and $S_a$ for the shared-Z star at outer index $a$, equipped with the canonical fiber grading. Then for every fiber $h$, $$ (S_a)_{(h,h,H)}\cong C_{a,h}. $$ Here tensor isomorphism means mutual tensor restriction. This identifies each surviving star block with its original component, so any matrix-multiplication certificate for that component transfers to the star block.
-- source:
--   Canonical shared-Z star grading and component inclusions.

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_quotient

open MME Module PiTensorProduct CoupledCTensorPackaging
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_primary_hash_family_shared_Z_star_graded_component
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) :
    TensorObj.Isomorphic (componentObj G family a h)
      ((starGrading G family a).blockSubtensor (cTensorOneHOneAddress H h)) := by sorry
