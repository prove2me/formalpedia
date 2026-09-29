-- Prove2me | solution 1 for Catalog.Novelty.EmotionalChromaticNumber.emoChrom_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:54:28.383052+00:00
-- url     : https://prove2.me/submissions/a99f9b35-67ec-4f53-9a35-5a56ff77bfb0

import Mathlib
import Definitions.Def_Geometry_EmotionalChromaticNumber
open Catalog.Novelty.EmotionalChromaticNumber in
theorem solution {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k)
    (hc : G.Colorable k) : emoChrom G ≤ k := by
  -- `k` is one of the admissible numbers of emotions
  exact Nat.sInf_le ⟨hk, hc⟩
