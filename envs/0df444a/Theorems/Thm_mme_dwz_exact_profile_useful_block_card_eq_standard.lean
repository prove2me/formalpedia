-- Prove2me | Theorems.Thm_mme_dwz_exact_profile_useful_block_card_eq_standard
-- name    : mme_dwz_exact_profile_useful_block_card_eq_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:00:40.885903+00:00
-- url     : https://prove2.me/theorems/ad15ae3c-c097-4d5f-b5b3-073db540e4b0
-- title:
--   Exact-profile Table-2 words have the standard useful-block cardinality
-- statement:
--   Fix a Table-2 scaling parameter $m$ and any source-order component word whose fifteenth joint histogram is the prescribed Table-2 histogram. Reindexing positions identifies its useful fine-$Z$ blocks with the canonical grouped standard blocks. Hence
--
--   $$|\operatorname{UsefulBlock}_m(\mathrm{outer})|=|\operatorname{DWZStandardBlock}_m|.$$
--
--   This ordering-independent equality supplies the common denominator used to convert aggregate nonhole counts into aggregate nonhole fractions.
-- source:
--   Duan--Wu--Zhou Table-2 useful-block construction and source-to-grouped position reindexing.

import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_exact_profile_useful_block_card_eq_standard
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m) :
    Fintype.card (MME.DWZTable2StandardForm.UsefulBlock m outer) =
      Fintype.card (MME.DWZComponentRestriction.DWZStandardBlock m) := by
  sorry
