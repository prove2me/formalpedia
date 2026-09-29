-- Prove2me | Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard
-- name    : mme_dwz_table2_broken_copy_transport_to_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:09:27.888026+00:00
-- url     : https://prove2.me/theorems/b426aa9e-a1ba-4831-a85d-9b14ea7a5641
-- title:
--   Exact Table-2 histograms transport broken copies to grouped standard coordinates
-- statement:
--   An exact Table-2 outer histogram canonically regroups the source positions by the fifteen component rows. This induces an equivalence from literal source-order useful blocks to the grouped standard-block labels. Mapping a broken copy's finite nonhole set along this equivalence preserves its cardinality and preserves membership for every literal useful block. In particular, the seven-eighths nonhole certificate used by the Hole Lemma is unchanged by regrouping.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4, Definition 6.3, and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_dwz_standard_labelled_z_blocks

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_table2_broken_copy_transport_to_standard
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer)) :
    ∃ positionEquiv :
        MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (positionEquiv p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ blockEquiv :
          MME.DWZTable2StandardForm.UsefulBlock m outer ≃
            MME.DWZComponentRestriction.DWZStandardBlock m,
        (∀ small p,
          (blockEquiv small).1 p = small.1 (positionEquiv p)) ∧
        ∃ transported : MME.DWZSquare.BrokenBlockCopy
            (MME.DWZComponentRestriction.DWZStandardBlock m),
          transported.nonholes.card = copy.nonholes.card ∧
          ∀ small,
            blockEquiv small ∈ transported.nonholes ↔
              small ∈ copy.nonholes := by
  sorry
