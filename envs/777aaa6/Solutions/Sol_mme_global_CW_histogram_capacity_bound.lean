-- Prove2me | solution 1 for mme_global_CW_histogram_capacity_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:24:39.316054+00:00
-- url     : https://prove2.me/submissions/63dd3f03-a8ab-4ba5-b718-57c51bb762b9

import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_recursive_region_word_capacity_bound
open BigOperators MME MME.RecursiveYZ MME.GlobalCW MME.CompleteSplit
set_option autoImplicit false

theorem solution {ell M : ℕ} (D : HistogramFrame ell M) (mu : D.Profile) :
    D.capacity mu ≤ 7 ^ (3 * M) := by
  have hcard : Fintype.card (Place D.n) = D.L := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr D.positions).symm
  have h := mme_recursive_region_word_capacity_bound ell (cell D.reference)
    (fun c i ↦ (c.2.val i).val) mu
  simpa only [hcard,D.length] using h
