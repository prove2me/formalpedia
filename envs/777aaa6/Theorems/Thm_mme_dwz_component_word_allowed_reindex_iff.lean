-- Prove2me | Theorems.Thm_mme_dwz_component_word_allowed_reindex_iff
-- name    : mme_dwz_component_word_allowed_reindex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:15:54.754648+00:00
-- url     : https://prove2.me/theorems/aca49a86-0092-462e-8a9a-145123490c83
-- title:
--   Table-2 component availability is invariant under position shuffling
-- statement:
--   Fix one of the fifteen Table-2 components and a canonical $Z$-basis word of the prescribed component power. The word is available when each left fine grade occurs with exactly its prescribed Table-2 multiplicity. For every permutation of the repeated component positions, the reindexed word is available if and only if the original word is available.
--
--   Thus the shuffling group preserves the exact $Z$-word subspace retained in the DWZ standard-form component, including at scale $m=0$. This is the index-level form of Claim 5.8 needed before lifting the shuffle to the tensor automorphism of Claim 5.9.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4, Definition 5.7, and Claim 5.8, PDF pp. 48--49 / printed pp. 47--48; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_component_word_allowed_reindex_iff
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm
      (Fin (MME.DWZTable2Counts.component s * m)))
    (w : MME.DWZComponentRestriction.PowIndex
      (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) :
    MME.DWZComponentRestriction.componentWordAllowed s m
        (MME.DWZComponentRestriction.PowIndex.reindex e w) ↔
      MME.DWZComponentRestriction.componentWordAllowed s m w := by
  sorry
