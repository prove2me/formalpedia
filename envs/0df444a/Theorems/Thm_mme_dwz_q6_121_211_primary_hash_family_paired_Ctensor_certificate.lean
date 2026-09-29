-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_primary_hash_family_paired_Ctensor_certificate
-- name    : mme_dwz_q6_121_211_primary_hash_family_paired_Ctensor_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-27T10:33:57.314015+00:00
-- url     : https://prove2.me/theorems/576f3a5e-04f9-4355-8e50-65ab66950b51
-- title:
--   Rows 121/211: source-faithful paired C-tensor family certificate
-- statement:
--   Fix Table-2 row $121$ or $211$ at scale $m$, and let a primary $q=6$ hash family have $A$ outer fibers of common size $H$ and exact profile $(L,L,2G)$. The literal allowed-word component power paired with its first-two-mode swap carries a source-faithful family of $A$ C-tensor stars. Each star has $H$ supported components sharing its third-mode block; each component is isomorphic to some matrix-multiplication tensor $\langle m_h,n_h,p_h\rangle$, and all components have the common volume
--
--   $$m_h n_h p_h = 6^{4G+2L}.$$
--
--   The component shapes may depend on the address and on the half-word split. Only their common volume is asserted. This is the invariant required by cyclic balancing and avoids imposing a false fixed orientation on the projected source.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 3.3 and 5.2-5.4 and Section 6.3; D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, 1990, pp. 270-272.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_primary_hash_family_paired_Ctensor_certificate
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H) :
    Nonempty (CTensorOneHOneFamilyCertificate
      (TensorObj.kron (restrictedComponentPower K s m)
        (TensorObj.permObj swapFirstTwoPerm
          (restrictedComponentPower K s m)))
      A H (6 ^ (4 * G + 2 * L))) := by
  sorry
