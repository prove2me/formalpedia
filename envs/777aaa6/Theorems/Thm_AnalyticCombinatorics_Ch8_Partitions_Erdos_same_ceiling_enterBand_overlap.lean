-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_same_ceiling_enterBand_overlap
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.same_ceiling_enterBand_overlap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:41:31.75098+00:00
-- url     : https://prove2.me/theorems/4e2e6bfe-8b17-414b-a03c-e2ea5c54bf0f
-- title:
--   Supporting lemma: same ceiling enterBand overlap
-- statement:
--   **L4 — same-ceiling first-entrance value overlap.**  There is `β > 0` so that eventually in `R`,
--   any two values `x, y` of the ceiling rank `T = R + A R` have *first-entrance* overlap `≥ β` on the
--   in-band slice into the band `ceilBand R (A R)`.  Lifts the one-step overlap (brick 7) via the banked
--   `min_Pker_le_min_enterBandKer_sum` (`Pker x z ≤ enterBandKer Pker B x z` on in-band targets).
--
--   The full literal source contract is:
--
--   ```lean
--   lemma same_ceiling_enterBand_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
--       ∃ β : ℝ, 0 < β ∧
--         ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
--           β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
--                 min (enterBandKer Pker (ceilBand R (A R)) x z)
--                     (enterBandKer Pker (ceilBand R (A R)) y z)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CeilingValueWindow.lean#L466. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance_x1
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# TASK L4 (R8 elementary route): same-ceiling value overlap via the divisor-self bound `σ(m) ≥ m`

The variable rank-band engine needs a positive in-band overlap (L4): for two starts `x, y` at the
same ceiling rank `T = R + A R`, the first-entrance laws into the band `ceilBand R (A R)` overlap by
`≥ β` on the in-band slice `{R ≤ rnk z}`.  By the banked one-step reduction
`min_Pker_le_min_enterBandKer_sum` this reduces to a positive overlap of the **one-step** predecessor
laws `Pker x ·`, `Pker y ·` on the slice.

R8's elementary idea (`/tmp/ac_a_uniform.txt`): a single **common value window**
`W_T = [ (T+1)²/9 − 2T , T²/9 − T ] ∩ ℕ` (length `~7T/9`) sits below every ceiling-rank value `x`,
inside the engine slice, and carries `Pker x z ≥ c/T` for EVERY same-ceiling `x` and `z ∈ W_T`.
The lower bound uses ONLY the trivial divisor-self bound `σ(x−z) ≥ x−z ≥ T` (no two-point divisor
estimate, no `KernelWindow`).  A constant minorant `η = c/T` on `S = W_T` with `|W_T| ≥ q·T` gives
overlap `≥ (c/T)(q·T) = cq =: β > 0` via the banked `overlap_ge_of_minorization`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

open Filter Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Brick 1 — the divisor-self bound `σ(m) ≥ m`. -/


/-! ## Brick 2 — the common value window. -/

/-! ## Brick 3 — window geometry: jump and sqrt bounds. -/


/-! ## Brick 4 — the window lies in the in-band slice. -/


/-! ## Brick 5 — pointwise `Pker` lower bound on the window. -/


/-! ## Brick 6 — linear cardinality of the window. -/


/-! ## Brick 7 — one-step same-ceiling value overlap. -/


/-! ## Brick 8 — lift to the first-entrance overlap (this is L4). -/

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.same_ceiling_enterBand_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ β : ℝ, 0 < β ∧
      ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
        β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (A R)) x z)
                  (enterBandKer Pker (ceilBand R (A R)) y z) := by sorry
