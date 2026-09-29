-- Prove2me | solution 1 for StoneDualityML.hammingDist_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T00:17:19.910356+00:00
-- url     : https://prove2.me/submissions/2ff1191b-985f-42e9-86a7-240be0ace589

import Mathlib
import Definitions.Def_Bridges_StoneDualityMLCore

theorem solution (n : ℕ) (h₁ h₂ : Fin n → Bool) :
    StoneDualityML.hammingDist n h₁ h₂ ≤ n := by
  unfold StoneDualityML.hammingDist
  exact le_trans (Finset.card_filter_le _ _) (by simp)
