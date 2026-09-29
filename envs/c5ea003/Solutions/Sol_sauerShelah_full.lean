-- Prove2me | solution 1 for sauerShelah_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:41:24.226036+00:00
-- url     : https://prove2.me/submissions/723149da-17c8-4f18-92fe-29d888d92f94

import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations
open ConceptFamily in
theorem solution (k : ℕ) : sauerShelahBound k k = 2 ^ k := by
  unfold sauerShelahBound
  exact Nat.sum_range_choose k
