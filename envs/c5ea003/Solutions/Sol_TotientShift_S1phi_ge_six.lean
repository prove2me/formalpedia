-- Prove2me | solution 1 for TotientShift.S1phi_ge_six
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:52:08.495418+00:00
-- url     : https://prove2.me/submissions/c0f135a1-dc4e-4962-8694-42c9871daf06

import Mathlib
import Definitions.Def_Bridges_TotientUnitShift
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
open Nat Finset TotientShift in
theorem solution : 6 ≤ S1phi 194 := by
  simp only [S1phi]
  rw [show (6 : ℕ) = ({1, 3, 15, 104, 164, 194} : Finset ℕ).card from by decide]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
