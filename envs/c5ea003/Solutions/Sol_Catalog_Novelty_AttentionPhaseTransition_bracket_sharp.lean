-- Prove2me | solution 1 for Catalog.Novelty.AttentionPhaseTransition.bracket_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:06.565789+00:00
-- url     : https://prove2.me/submissions/bd9be574-e066-4888-b03b-235452cbfff7

-- Sol generated from Novelty/AttentionPhaseTransition.lean
import Mathlib
import Definitions.Def_Novelty_AttentionPhaseTransition
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_AttentionScaleThreshold
import Theorems.Thm_Catalog_Novelty_AttentionRetentionKnee_knee_le
import Theorems.Thm_Catalog_Novelty_AttentionRetentionKnee_knee_spec
import Theorems.Thm_Catalog_Novelty_AttentionRetentionKnee_retained_mono

/-!
# The increment accelerates at 4096: a phase transition in the attention budget (NET-78)

NET-78 extends the 0.5B knee chain of NET-67 by one context octave.  Writing
`j` for the number of context doublings above the base context `512`
(so `j = 0,1,2,3` is `ctx = 512, 1024, 2048, 4096`), the measured knees are

| j        | 0  | 1  | 2  | 3  |
|----------|----|----|----|----|
| `k*`     | 16 | 20 | 24 | 40 |

with increments `+4, +4, +16`.  The verdict extracted from the run is
**THE-INCREMENT-ACCELERATES-AT-4096**: the affine law `16 + 4j` of cycle 1
(`Novelty.AttentionBudgetIncrement`) breaks at the fourth doubling.

This file is the formal audit of that verdict.  It has four layers.

**1. Discrete layer.**  `kneeSmall_refuted` and `no_affine_fits` prove the two
refutations exactly (`P1`: the `+4` law does not continue; `P2`: no saturation).
But the four data points are far from determining the continuation:
`kneeRamp`, `kneeCubic` and `kneeQuad` all reproduce `16, 20, 24, 40` and
predict `56`, `80`, `92` at `ctx = 8192` (`fits_underdetermined`).  What *is*
forced, under the (measured) discrete convexity of the chain, is a sharp lower
bound: `convex_growth` gives `f (m+3) ≥ 40 + 16m`, hence at least `56` keys at
`8192` and no finite universally safe budget (`no_uniform_budget`).

**2. Tropical layer.**  The minimal convex fit is a two-term max-plus
polynomial, `kneeRamp j = max (16 + 4j) (16j - 8)` (`kneeRamp_eq_max`), and its
tropical corner — the unique crossing of the two affine pieces — sits at
`j = 2`, i.e. at `ctx = 2048` (`transition_at_2048`).  So "budgets are stable
for the first ~2000 tokens, then sharply more expensive" is not a narrative
gloss: it is the location of the tropical root of the fitted budget law.

**3. Gate layer (barrier (c), confronted).**  The knee was read on the coarse
grid `{16,20,24,28,32,40}`, so the reported `40` is a grid point, not a
measurement.  `gate_bracket` recovers the gate `τ` from the table
(`0.979 < τ ≤ 0.984`), `true_knee_bracket` shows every profile consistent with
the table has its true knee in `[33, 40]`, and `bracket_sharp` exhibits two
explicit profiles realising both endpoints.  Consequently
`acceleration_bracketed`: the data force an increment in `[9, 16]`, i.e. an
acceleration factor in `[9/4, 4]`.  **The direction of the verdict is proved;
the advertised factor `4` is the top of a bracket whose bottom is `2.25`.**

**4. Continuous layer.**  Cycle 1 derived the `+4` law from a decay rate
degrading as `λ_j = λ₀/(j+1)`.  `lamAt_law_refuted` shows that family is now
strictly refuted: it is affine in `j`, and the chain is not.
`rate_collapse_accelerates` replaces it with a *model-free* consequence: for any
exponential-tail explanation of the chain, `λ_j = log(1/δ)/k_j`, so
`λ₃/λ₂ < λ₂/λ₁` — and `rate_collapse_accelerates_robust` proves this
**for every knee value in the grid bracket `[33,40]`**.  The phase transition
therefore survives the grid gap even though the factor `4` does not.  Finally
`calibration_phase` calibrates the crossover rate family `lamCross` against the
whole measured chain at the cycle-1 tail budget `δ = e⁻⁴`.

**Deployment.**  `cache24_fails_robust` proves the deployment corollary in its
grid-robust form: a 24-key cache fails at `ctx = 4096` for *every* profile
consistent with the table, and `provably_unsafe` / `certified_safe` delimit
exactly which budgets the measurement decides.
-/

open Catalog.Novelty.AttentionPhaseTransition

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. The measured chain and the death of the affine law -/





/-! ### 2. Three continuations, all fitting the same four points -/









/-! ### 3. What convexity does force -/









/-! ### 4. Tropical layer: the transition is a max-plus corner at ctx = 2048 -/




/-! ### 5. Gate layer: the coarse grid and what it really proves -/







theorem pLow_nonneg (i : ℕ) : 0 ≤ pLow i := by
  unfold pLow
  split_ifs <;> norm_num

theorem pHigh_nonneg (i : ℕ) : 0 ≤ pHigh i := by
  unfold pHigh
  split_ifs <;> norm_num

theorem pLow_table : MatchesTable pLow := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [retained, Finset.sum_range_succ, pLow] <;> norm_num

theorem pHigh_table : MatchesTable pHigh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [retained, Finset.sum_range_succ, pHigh] <;> norm_num

theorem retained_pLow_33 : retained pLow 33 = 984 / 1000 := by
  simp [retained, Finset.sum_range_succ, pLow]; norm_num

theorem retained_pHigh_39 : retained pHigh 39 = 979 / 1000 := by
  simp [retained, Finset.sum_range_succ, pHigh]; norm_num


/-! ### 6. Deployment: which budgets the measurement decides -/





/-! ### 7. Continuous layer: the rate law of cycle 1 is refuted -/





/-! ### 8. A crossover rate family that fits the whole chain -/









open Catalog.Novelty.AttentionPhaseTransition in
theorem solution:
    MatchesTable pLow ∧ MatchesTable pHigh ∧
      knee pLow (98 / 100) = 33 ∧ knee pHigh (98 / 100) = 40 := by
  refine ⟨pLow_table, pHigh_table, ?_, ?_⟩
  · refine le_antisymm (knee_le (by rw [retained_pLow_33]; norm_num)) ?_
    by_contra hcon
    have hle : knee pLow (98 / 100) ≤ 32 := by omega
    have hex : ∃ k, (98 : ℝ) / 100 ≤ retained pLow k :=
      ⟨33, by rw [retained_pLow_33]; norm_num⟩
    have h1 := knee_spec hex
    have h2 : retained pLow (knee pLow (98 / 100)) ≤ retained pLow 32 :=
      retained_mono pLow_nonneg hle
    rw [pLow_table.2.2.2.2.1] at h2
    linarith
  · refine le_antisymm (knee_le (by rw [pHigh_table.2.2.2.2.2]; norm_num)) ?_
    by_contra hcon
    have hle : knee pHigh (98 / 100) ≤ 39 := by omega
    have hex : ∃ k, (98 : ℝ) / 100 ≤ retained pHigh k :=
      ⟨40, by rw [pHigh_table.2.2.2.2.2]; norm_num⟩
    have h1 := knee_spec hex
    have h2 : retained pHigh (knee pHigh (98 / 100)) ≤ retained pHigh 39 :=
      retained_mono pHigh_nonneg hle
    rw [retained_pHigh_39] at h2
    linarith
