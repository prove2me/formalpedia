-- Prove2me | solution 1 for mme_dwz_fourth_exact_log_scale_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T17:54:35.276684+00:00
-- url     : https://prove2.me/submissions/d0e77ff2-a38d-4d9c-85c1-cfd22f7212f7

import Definitions.Def_mme_dwz_fourth_log_scale_table_data
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational

open MME.DWZFourthLogScaleTable

set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem chunk0_valid : chunk0.all entryValid = true := by decide +kernel
private theorem chunk1_valid : chunk1.all entryValid = true := by decide +kernel
private theorem chunk2_valid : chunk2.all entryValid = true := by decide +kernel
private theorem chunk3_valid : chunk3.all entryValid = true := by decide +kernel
private theorem chunk4_valid : chunk4.all entryValid = true := by decide +kernel
private theorem chunk5_valid : chunk5.all entryValid = true := by decide +kernel
private theorem chunk6_valid : chunk6.all entryValid = true := by decide +kernel
private theorem chunk7_valid : chunk7.all entryValid = true := by decide +kernel
private theorem chunk8_valid : chunk8.all entryValid = true := by decide +kernel
private theorem chunk9_valid : chunk9.all entryValid = true := by decide +kernel
private theorem chunk10_valid : chunk10.all entryValid = true := by decide +kernel
private theorem chunk11_valid : chunk11.all entryValid = true := by decide +kernel
private theorem chunk12_valid : chunk12.all entryValid = true := by decide +kernel
private theorem chunk13_valid : chunk13.all entryValid = true := by decide +kernel
private theorem chunk14_valid : chunk14.all entryValid = true := by decide +kernel
private theorem chunk15_valid : chunk15.all entryValid = true := by decide +kernel
private theorem chunk16_valid : chunk16.all entryValid = true := by decide +kernel
private theorem chunk17_valid : chunk17.all entryValid = true := by decide +kernel
private theorem chunk18_valid : chunk18.all entryValid = true := by decide +kernel
private theorem chunk19_valid : chunk19.all entryValid = true := by decide +kernel
private theorem chunk20_valid : chunk20.all entryValid = true := by decide +kernel
private theorem chunk21_valid : chunk21.all entryValid = true := by decide +kernel
private theorem chunk22_valid : chunk22.all entryValid = true := by decide +kernel
private theorem chunk23_valid : chunk23.all entryValid = true := by decide +kernel
private theorem chunk24_valid : chunk24.all entryValid = true := by decide +kernel
private theorem chunk25_valid : chunk25.all entryValid = true := by decide +kernel
private theorem chunk26_valid : chunk26.all entryValid = true := by decide +kernel
private theorem chunk27_valid : chunk27.all entryValid = true := by decide +kernel
private theorem chunk28_valid : chunk28.all entryValid = true := by decide +kernel
private theorem chunk29_valid : chunk29.all entryValid = true := by decide +kernel
private theorem chunk30_valid : chunk30.all entryValid = true := by decide +kernel

private theorem entries_all_valid : entries.all entryValid = true := by
  simp [entries, chunk0_valid, chunk1_valid, chunk2_valid, chunk3_valid, chunk4_valid, chunk5_valid, chunk6_valid, chunk7_valid, chunk8_valid, chunk9_valid, chunk10_valid, chunk11_valid, chunk12_valid, chunk13_valid, chunk14_valid, chunk15_valid, chunk16_valid, chunk17_valid, chunk18_valid, chunk19_valid, chunk20_valid, chunk21_valid, chunk22_valid, chunk23_valid, chunk24_valid, chunk25_valid, chunk26_valid, chunk27_valid, chunk28_valid, chunk29_valid, chunk30_valid]

theorem solution :
    (forall i : Fin entries.size,
      0 < argument i /\ 1 <= argument i * 2 ^ scale i) /\
    forall i : Fin entries.size,
      (MME.autoScaledLogLower (argument i) (scale i) 6 : Real) <=
          Real.log (argument i : Real) /\
        Real.log (argument i : Real) <=
          (MME.autoScaledLogUpper (argument i) (scale i) 6 : Real) := by
  refine ⟨?_, ?_⟩
  · intro i
    apply of_decide_eq_true
    exact (Array.all_eq_true.mp entries_all_valid) i i.isLt
  · intro i
    have h : 0 < argument i /\ 1 <= argument i * 2 ^ scale i := by
      apply of_decide_eq_true
      exact (Array.all_eq_true.mp entries_all_valid) i i.isLt
    exact mme_log_interval_of_auto_scaled_rational
      (argument i) (scale i) 6 h.1 h.2
