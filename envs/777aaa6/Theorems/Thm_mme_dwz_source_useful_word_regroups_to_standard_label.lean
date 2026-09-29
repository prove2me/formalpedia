-- Prove2me | Theorems.Thm_mme_dwz_source_useful_word_regroups_to_standard_label
-- name    : mme_dwz_source_useful_word_regroups_to_standard_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:48:09.805893+00:00
-- url     : https://prove2.me/theorems/ccc89098-e210-4bc5-a9b5-27f146f3276f
-- title:
--   Useful source Z words regroup to the exact standard-block label
-- statement:
--   Regroup a retained source address by an outer-label-preserving equivalence from the canonical Table-2 positions. If a canonical source $Z$-basis word has the exact componentwise split histograms of a useful word, then it determines a grouped available word $W_g$. At every grouped position $p$, the fine pair carried by $W_g$ equals the fine pair of the original word at the corresponding source position. Consequently the standard useful-block label of $W_g$ is exactly the image of the literal source useful block under any block equivalence induced by the same position regrouping. This is a literal label identity, not a cardinality comparison.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.4--5.5 and Definition 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_source_useful_word_regroups_to_standard_label
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      MME.DWZComponentRestriction.groupedOuter p)
    (blockEquiv : MME.DWZTable2StandardForm.UsefulBlock m outer ≃
      MME.DWZComponentRestriction.DWZStandardBlock m)
    (hblock : ∀ small p,
      (blockEquiv small).1 p = small.1 (e p))
    (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
    (hW : MME.DWZSourceAligned.addressWordUseful m outer W) :
    ∃ Wg : MME.DWZComponentRestriction.GroupedAllowedWords.{u} m,
      (∀ p, MME.DWZComponentRestriction.groupedFineZ Wg p =
        MME.DWZSourceAligned.addressFineZ W (e p)) ∧
      MME.DWZComponentRestriction.groupedUsefulBlock m Wg =
        blockEquiv
          (MME.DWZSourceAligned.addressUsefulBlock m outer W hW) := by
  sorry
