-- Prove2me | Theorems.Thm_mme_dwz_source_raw_component_words_allowed_iff_useful
-- name    : mme_dwz_source_raw_component_words_allowed_iff_useful
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:15:27.951333+00:00
-- url     : https://prove2.me/theorems/93f15294-6a3e-4f68-bc45-06da59fb999c
-- title:
--   Raw Table-2 component availability is equivalent to source-word usefulness
-- statement:
--   Let the grouped positions of the fifteen Table-2 component powers be identified with the source positions by an equivalence preserving each Table-2 row. Suppose a grouped raw word and a source word carry the same canonical $Z$-letter at every corresponding position. Then all fifteen raw component words satisfy their prescribed left-split histograms if and only if the source word satisfies the corresponding useful-word histograms. This is the exact semantic bridge between the component projectors and the source-side useful-block condition.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4, Table 2, and the component regrouping in Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_source_raw_component_words_allowed_iff_useful
    {N m : ℕ} {outer : Fin N → Fin 15}
    (e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      MME.DWZComponentRestriction.groupedOuter p)
    (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
    (raw : ∀ s : Fin 15,
      MME.DWZComponentRestriction.PowIndex
        (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ s))
        (MME.DWZTable2Counts.component s * m))
    (hraw : ∀ p : MME.DWZComponentRestriction.GroupedPosition m,
      HEq (MME.DWZComponentRestriction.PowIndex.get
          (MME.DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
        (W (e p))) :
    (∀ s, MME.DWZComponentRestriction.componentWordAllowed s m (raw s)) ↔
      MME.DWZSourceAligned.addressWordUseful m outer W := by
  sorry
