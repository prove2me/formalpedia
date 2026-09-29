-- Prove2me | solution 1 for TotientShift.S1phi_ge_ten
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:57:33.451185+00:00
-- url     : https://prove2.me/submissions/df7a5546-0ebf-4deb-88cc-e3061f48e164

import Mathlib
import Definitions.Def_Bridges_TotientUnitShift
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
open Nat Finset TotientShift in
theorem solution : 10 ≤ S1phi 975 := by
  simp only [S1phi]
  rw [show (10 : ℕ) = ({1, 3, 15, 104, 164, 194, 255, 495, 584, 975} : Finset ℕ).card from by decide]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
