-- Prove2me | Definitions.Def_Novelty_AttentionScaleThreshold
-- name    : Novelty_AttentionScaleThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:05:53.270827+00:00
-- url     : https://prove2.me/theorems/e81aea58-64bc-456a-b289-2a91e8e94664
-- title:
--   Aether Catalog definitions — Novelty_AttentionScaleThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AttentionScaleThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AttentionScaleThreshold.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee

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

namespace Catalog.Novelty.AttentionScaleThreshold

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. Hinges: what the measured triple does and does not determine -/

/-- A *hinge* budget law: a floor (the minimum viable key count) below which the
affine demand `base + slope·j` is invisible. -/
def hinge (floor base slope j : ℕ) : ℕ := max floor (base + slope * j)



/-- The measured 1.5B triple `16, 16, 18`, as a constraint on hinge parameters
with the measured floor `16`. -/
def HingeFits (base slope : ℕ) : Prop :=
  hinge 16 base slope 0 = 16 ∧ hinge 16 base slope 1 = 16 ∧ hinge 16 base slope 2 = 18








/-! ### 2. Grid resolution: why a coarse sweep over-reads the knee -/

/-- The knee as measured on the grid of multiples of `d`. -/
noncomputable def kneeMul (p : ℕ → ℝ) (tau : ℝ) (d : ℕ) : ℕ :=
  sInf {k | d ∣ k ∧ tau ≤ retained p k}





/-! ### 3. The scale exponent and the context-free threshold -/

/-- The scale exponent calibrated by the two measured cells: peakedness `λ₀`
grows like `N^θ` in the parameter count, and `λ₀` doubles from `0.5B` to `1.5B`,
so `3^θ = 2`. -/
noncomputable def theta : ℝ := Real.log 2 / Real.log 3




/-- Peakedness of a model with `N` billion parameters, calibrated so that
`λ₀(0.5) = 1` and `λ₀(1.5) = 2`. -/
noncomputable def lam0Of (N : ℝ) : ℝ := (2 * N) ^ theta

/-- Predicted keys-per-doubling increment at parameter count `N` (in billions):
the cycle-1 increment `log(1/δ)/λ₀` at tail budget `δ = e⁻⁴`. -/
noncomputable def incrAt (N : ℝ) : ℝ := 4 * (2 * N) ^ (-theta)











end Catalog.Novelty.AttentionScaleThreshold


