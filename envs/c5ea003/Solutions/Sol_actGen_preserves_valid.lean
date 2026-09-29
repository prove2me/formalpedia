-- Prove2me | solution 1 for actGen_preserves_valid
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:56:16.184268+00:00
-- url     : https://prove2.me/submissions/307ad268-ef7e-475a-a3f0-dae335716aa8

import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability
theorem solution (g : BergGen) {p : ℤ × ℤ} (hp : ValidPair p) : ValidPair (actGen g p) := by
  obtain ⟨h1, h2⟩ := hp
  cases g <;> (simp only [ValidPair, actGen]; omega)
