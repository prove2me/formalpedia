-- Prove2me | Theorems.Thm_mme_CW_2376_profile_rate_tendsto
-- name    : mme_CW_2376_profile_rate_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:56:03.025407+00:00
-- url     : https://prove2.me/theorems/d2937d34-9b3d-4087-877d-1dcbec2f3e86
-- title:
--   The explicit CW profile loss envelope vanishes
-- statement:
--   The explicit envelope $$r_m=\frac{1}{\sqrt{\sqrt{m+1}}}$$ is nonnegative and converges to zero. Its $m^{-1/4}$ decay is deliberately slower than the $O(m^{-1/2})$ per-root Behrend loss and the $O(\log m/m)$ multinomial losses, so it can absorb both at sufficiently large scales.
-- source:
--   Elementary real-analysis envelope for the explicit Behrend bound used in Coppersmith--Winograd (1990), journal pp. 267--269.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_2376_profile_data
open MME Filter

theorem mme_CW_2376_profile_rate_tendsto :
    Tendsto cw2376ProfileRate atTop (nhds 0) ∧
      ∀ m : ℕ, 0 ≤ cw2376ProfileRate m := by
  sorry
