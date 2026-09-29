-- Prove2me | solution 1 for RLHF.IsPosDist.isDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:33:03.734401+00:00
-- url     : https://prove2.me/submissions/ab1cac21-947c-4680-9c10-f389077284e7

import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsPosDist p) : IsDist p := by
  obtain ⟨hpos, hsum⟩ := hp
  exact ⟨fun y => (hpos y).le, hsum⟩
