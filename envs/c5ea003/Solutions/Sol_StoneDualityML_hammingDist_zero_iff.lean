-- Prove2me | solution 1 for StoneDualityML.hammingDist_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T00:23:38.97665+00:00
-- url     : https://prove2.me/submissions/3c49f489-0c5e-49ab-b135-7f571a524cbb

import Mathlib
import Definitions.Def_Bridges_StoneDualityMLCore

theorem solution (n : ℕ) (h₁ h₂ : Fin n → Bool) :
    StoneDualityML.hammingDist n h₁ h₂ = 0 ↔ h₁ = h₂ := by
  simp only [StoneDualityML.hammingDist, Finset.card_filter_eq_zero_iff,
    Finset.mem_univ, true_implies, not_not]
  exact funext_iff.symm
