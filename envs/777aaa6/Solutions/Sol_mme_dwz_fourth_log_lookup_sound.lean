-- Prove2me | solution 1 for mme_dwz_fourth_log_lookup_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:47:34.902268+00:00
-- url     : https://prove2.me/submissions/5761c3e5-b798-4146-b6bb-647ac9188873

import Theorems.Thm_mme_dwz_fourth_exact_log_scale_table
import Definitions.Def_mme_dwz_fourth_log_scale_table_data

open MME MME.DWZFourthLogScaleTable
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthLogScaleTable

theorem entries_all_valid : entries.all entryValid = true := by
  rw [Array.all_eq_true]
  intro i hi
  exact decide_eq_true (mme_dwz_fourth_exact_log_scale_table.1 ⟨i, hi⟩)

end MME.DWZFourthLogScaleTable

namespace MME.DWZFourthLogScaleTable

private theorem certificate_of_lookup {index : Nat} {entry : Prod Rat Nat}
    (hlookup : entries[index]? = some entry) :
    0 < entry.1 /\
      (MME.autoScaledLogLower entry.1 entry.2 6 : Real) <=
          Real.log (entry.1 : Real) /\
        Real.log (entry.1 : Real) <=
          (MME.autoScaledLogUpper entry.1 entry.2 6 : Real) := by
  obtain ⟨hindex, hget⟩ := Array.getElem?_eq_some_iff.mp hlookup
  have hvalidAt : entryValid entries[index] = true :=
    (Array.all_eq_true.mp entries_all_valid) index hindex
  have hvalidEntry : entryValid entry = true := by
    simpa only [hget] using hvalidAt
  have hvalid : 0 < entry.1 /\ 1 <= entry.1 * 2 ^ entry.2 := by
    exact of_decide_eq_true hvalidEntry
  exact ⟨hvalid.1,
    mme_log_interval_of_auto_scaled_rational
      entry.1 entry.2 6 hvalid.1 hvalid.2⟩

end MME.DWZFourthLogScaleTable

theorem solution :
    ∀ {index : Nat} {entry : Prod Rat Nat} (hlookup : entries[index]? = some entry),
    0 < entry.1 /\
      (MME.autoScaledLogLower entry.1 entry.2 6 : Real) <=
          Real.log (entry.1 : Real) /\
        Real.log (entry.1 : Real) <=
          (MME.autoScaledLogUpper entry.1 entry.2 6 : Real) :=
  certificate_of_lookup
