-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
-- name    : mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-27T10:53:07.116473+00:00
-- url     : https://prove2.me/theorems/c051de0d-6df0-41aa-b933-9cce3a78a8e5
-- title:
--   Rows 121/211: absorbed ambient C-tensor certificate under a common halving
-- statement:
--   Work first in the unprojected pair of the canonical $q=6$ Table-2 component powers for row $121$ or $211$, with the second factor transposed in its first two tensor modes. Given an induced primary family and one common balanced halving, there are $A$ C-tensor stars and a finite mode-choice certificate mapping the ambient pair to their direct sum. Each star has $H$ matrix-multiplication components of volume $6^{4G+2L}$.
--
--   In addition, every individual mode-choice map absorbs the canonical paired allowed-word projector. This last condition is the source-faithfulness interface: it permits the ambient construction to descend exactly to the literal paired restricted component, rather than incorrectly replacing that source by an unrestricted coupled tensor.
--
--   This theorem isolates the remaining basis-labelled construction: concatenate the two powered row routers through the common position halving, use inducedness to kill mixed choices, and use the two balanced half-histograms to prove projector absorption.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent and C-tensor extraction on journal pp. 266-271; Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2-5.4 and Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_CW_q6_common_paired_halving
import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_induced_mode_choice_certificate

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    ∃ star : Fin A → TensorObj K 3,
      ∃ cert : InducedModeChoiceCertificate
        (componentPairAmbient K s m) (TensorObj.bigAdd star),
        (∀ (i : Fin 3) (slot : Fin (cert.slotCount i)),
          (cert.modeMap i slot).comp (componentPairProject K s m i) =
            cert.modeMap i slot) ∧
        Nonempty (∀ a : Fin A,
          CTensorOneHOneCertificate (star a) H
            (6 ^ (4 * G + 2 * L))) := by
  sorry
