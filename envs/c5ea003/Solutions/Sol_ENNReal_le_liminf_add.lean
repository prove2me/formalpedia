-- Prove2me | solution 1 for ENNReal.le_liminf_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:06:16.030824+00:00
-- url     : https://prove2.me/submissions/53d04785-aac7-4a67-acc4-ef808b68a730

import Mathlib

open Filter

theorem solution {ι : Type*} (l : Filter ι) (F G : ι → ENNReal) :
    Filter.liminf F l + Filter.liminf G l
      ≤ Filter.liminf (fun x => F x + G x) l := by
  have hne : ∃ s : Set ι, s ∈ l := ⟨Set.univ, Filter.univ_mem⟩
  rw [Filter.liminf_eq_iSup_iInf (u := F), ENNReal.biSup_add' hne]
  refine iSup_le fun s => ?_
  refine iSup_le fun hs => ?_
  rw [Filter.liminf_eq_iSup_iInf (u := G), ENNReal.add_biSup' hne]
  refine iSup_le fun t => ?_
  refine iSup_le fun ht => ?_
  rw [Filter.liminf_eq_iSup_iInf (u := fun x => F x + G x)]
  refine le_trans ?_
    (le_iSup₂ (f := fun (r : Set ι) (_ : r ∈ l) => ⨅ a ∈ r, (F a + G a))
      (s ∩ t) (Filter.inter_mem hs ht))
  refine le_iInf₂ fun a ha => ?_
  exact add_le_add (iInf₂_le a ha.1) (iInf₂_le a ha.2)
