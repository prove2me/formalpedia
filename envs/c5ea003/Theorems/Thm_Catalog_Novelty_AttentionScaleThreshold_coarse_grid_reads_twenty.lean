-- Prove2me | Theorems.Thm_Catalog_Novelty_AttentionScaleThreshold_coarse_grid_reads_twenty
-- name    : Catalog.Novelty.AttentionScaleThreshold.coarse_grid_reads_twenty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:07:46.097176+00:00
-- url     : https://prove2.me/theorems/d1e08762-0f5c-4a0d-95ad-56d2899d5a65
-- title:
--   The NET-66 / NET-67 discrepancy, exactly.
-- statement:
--   **The NET-66 / NET-67 discrepancy, exactly.**  For a profile whose true knee
--   is `18`, a sweep restricted to the spacing-`4` grid `{16, 20, 24, …}` reports
--   `20` — one grid point high, precisely the coarse read that NET-67's two-point
--   addendum corrected.  The over-read is `2 < 4`, inside the resolution bound.
--
--   ```lean
--   theorem Catalog.Novelty.AttentionScaleThreshold.coarse_grid_reads_twenty:
--       knee (fun _ => (1 : ℝ)) 18 = 18 ∧ kneeMul (fun _ => (1 : ℝ)) 18 4 = 20 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AttentionScaleThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AttentionScaleThreshold.lean#L146

-- Thm stub generated from Novelty/AttentionScaleThreshold.lean
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_AttentionScaleThreshold

/-!
# Hinges, grid resolution, and the scale threshold (NET-67, cycle 2)

This is the second research cycle on the NET-67 measurement.  Cycle 1
(`Novelty.AttentionBudgetIncrement`, `Novelty.AttentionRetentionKnee`) fixed the
two measured budget laws, audited the verdict, and derived the additive law from
a decay rate degrading like `1/log(context)`.  Three questions were left open,
and each gets a theorem here.

**(1) How much does the measured triple actually determine?**  The 1.5B curve is
a *hinge* `max 16 (base + slope·j)`.  `hingeFits_iff` characterises all hinges
through the measured points `16, 16, 18`, and the answer is uncomfortable:
`hingeFits_slope_ge_two` shows the data only force `slope ≥ 2`, and
`hingeFits_alternative` exhibits a genuinely different fit (`base = 12`,
`slope = 3`).  So the advertised `+2` is a **lower bound**, not a measurement.
`hinge_prediction_discriminates` shows the two fits separate at the very next
octave (`20` versus `21` keys at `4096`), which is exactly the experiment to run.

**(2) Why did NET-66 read `20` where NET-67 reads `18`?**  Because a knee read
on a coarse grid is the least *grid point* above the true knee.  `kneeMul` is
the grid-restricted knee and `kneeMul_bounds` proves the two-sided estimate
`knee ≤ kneeMul < knee + d`.  `coarse_grid_reads_twenty` realises the NET-66/67
discrepancy exactly: a profile whose true knee is `18` is read as `20` on the
spacing-`4` grid, and the error is provably below the spacing.

**(3) Does the halving extrapolate to 7B?**  Cycle 1 calibrated the peakedness
of the two models to `λ₀ = 1` and `λ₀ = 2` at parameter counts `0.5B` and
`1.5B`, i.e. `λ₀(N) = (2N)^θ` with `θ = log 2 / log 3`.  The induced increment
law `incrAt N = 4·(2N)^(-θ)` reproduces both measurements
(`incrAt_half`, `incrAt_three_halves`), is strictly decreasing
(`incrAt_strictAntiOn`), and has an **exact closed-form threshold**:
`incrAt N < 1 ↔ 4.5 < N` (`incrAt_lt_one_iff`).  Hence
`scale_threshold_four_point_five`: *a model above 4.5B parameters needs less
than one extra key per context doubling* — its attention budget is essentially
context-free.  For the proposed 7B cell the prediction is bracketed exactly:
`1/2 < incrAt 7 < 1` (`prediction_7B`).
-/

open Catalog.Novelty.AttentionScaleThreshold

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. Hinges: what the measured triple does and does not determine -/












/-! ### 2. Grid resolution: why a coarse sweep over-reads the knee -/

theorem Catalog.Novelty.AttentionScaleThreshold.coarse_grid_reads_twenty:
    knee (fun _ => (1 : ℝ)) 18 = 18 ∧ kneeMul (fun _ => (1 : ℝ)) 18 4 = 20 := by sorry
