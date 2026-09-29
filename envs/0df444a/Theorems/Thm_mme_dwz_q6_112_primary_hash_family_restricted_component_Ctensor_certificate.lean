-- Prove2me | Theorems.Thm_mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
-- name    : mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T19:24:22.076561+00:00
-- url     : https://prove2.me/theorems/8cf5ba30-885f-4cc4-8503-f5f9fc1ece21
-- title:
--   Exact primary-hash C-tensor certificate for the restricted q=6 row-112 power
-- statement:
--   Let an induced primary hash family be given at the exact integer scale of the enhanced 112 row in the q=6 Duan–Wu–Zhou Table-2 distribution. Thus, with $t=20088623m$, its address parameters are $N=50000000t$, $L=21015t$, and $G=49978985t$, and it has $A$ outer fibers of common size $H$. Then the literal restricted row-112 component power contains a modewise direct sum of $A$ C-tensor stars over $\langle 1,H,1\rangle$, with every component matrix-multiplication tensor having common volume
--
--   $$
--   6^{4G+2L}.
--   $$
--
--   Unlike the unrestricted coupled-power certificate, this statement lands directly in the prescribed-histogram subtensor used by Table 2. It is the algebraic enhanced-112 child needed before applying the primary-hash rate estimate and balanced C-tensor extraction.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and the enhanced 112 analysis in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_standard_obj

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedComponentPower K (12 : Fin 15) m) A H
        (6 ^
          (4 * (49978985 * (20088623 * m)) +
            2 * (21015 * (20088623 * m))))) := by
  sorry
