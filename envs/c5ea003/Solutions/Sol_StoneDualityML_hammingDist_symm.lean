-- Prove2me | solution 1 for StoneDualityML.hammingDist_symm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T00:22:00.403297+00:00
-- url     : https://prove2.me/submissions/50d7a409-87a1-4825-80f5-fcba5b137c0e

import Mathlib
import Definitions.Def_Bridges_StoneDualityMLCore

theorem solution (n : ℕ) (h₁ h₂ : Fin n → Bool) :
    StoneDualityML.hammingDist n h₁ h₂ = StoneDualityML.hammingDist n h₂ h₁ := by
  simp only [StoneDualityML.hammingDist, ne_comm]
