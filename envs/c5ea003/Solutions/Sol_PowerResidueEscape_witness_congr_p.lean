-- Prove2me | solution 1 for PowerResidueEscape.witness_congr_p
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:01:33.321867+00:00
-- url     : https://prove2.me/submissions/e04643ce-8f99-4cbd-8982-d89d329b1eb0

import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_PowerResidueCriterion
theorem solution {M : ℕ} (hM : M ∣ 720720) : (137 : ℕ) % M = 720857 % M := by
  -- `720857 = 137 + 720720` and `M ∣ 720720`
  obtain ⟨k, hk⟩ := hM
  rw [show (720857 : ℕ) = 137 + M * k by omega, Nat.add_mul_mod_self_left]
