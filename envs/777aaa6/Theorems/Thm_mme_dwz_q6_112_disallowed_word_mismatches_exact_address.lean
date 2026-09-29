-- Prove2me | Theorems.Thm_mme_dwz_q6_112_disallowed_word_mismatches_exact_address
-- name    : mme_dwz_q6_112_disallowed_word_mismatches_exact_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:24:01.070662+00:00
-- url     : https://prove2.me/theorems/89302959-b77d-4254-a1f8-02deff008ed0
-- title:
--   Every disallowed canonical 112 word mismatches an exact enhanced address
-- statement:
--   Fix the enhanced q=6 coupled 112 profile at Table-2 scale m, and let a letter labelling translate each canonical left fine grade according to the coupled grade permutation 0,1,2 ↦ 2,0,1. If a canonical 112 Z-word fails the prescribed Table-2 histogram, then it must disagree with every exact enhanced coupled address at some position. Equivalently, pointwise agreement would force equality of all three grade-fiber cardinalities and hence availability. This is the finite combinatorial bridge from the exact address profile to address-projector vanishing.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and the exact profile/hashing construction in Sections 5–6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_q6_112_exact_profile_data
import Theorems.Thm_mme_dwz_q6_112_exact_address_allowed_histogram

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_112_disallowed_word_mismatches_exact_address
    (m : ℕ)
    (address : CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)))
    (labelGrade : LiftedCoarsePair.{u} 6 2 → Fin 3)
    (htranslate : ∀ p,
      p.leftGrade = mme_dwz_q6_coupled_Z_leftGrade (labelGrade p))
    (w : PowIndex (LiftedCoarsePair.{u} 6 2)
      (MME.DWZTable2Counts.component (12 : Fin 15) * m))
    (hnot : ¬ componentWordAllowed (12 : Fin 15) m w) :
    ∃ hlen : MME.DWZTable2Counts.component (12 : Fin 15) * m =
        2 * (50000000 * (20088623 * m)),
      ∃ r : Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m),
        labelGrade (PowIndex.get _ w r) ≠
          address.1 2 (Fin.cast hlen r) := by
  sorry
