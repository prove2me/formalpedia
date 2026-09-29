-- Prove2me | solution 1 for EdgeSpikeDefect.defect_mixK_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:48:31.809531+00:00
-- url     : https://prove2.me/submissions/1feb4630-5215-475d-884c-77f6aa9cd941

-- Sol generated from MachineLearning/EdgeSpikeKernelDefect.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeKernelDefect

/-!
# The three-bin log-convexity defect: kernel existence is identified, steepness is not

Companion to `MachineLearning.EdgeSpikeCensoring`.  That file shows that the
*steepness* `b` of a left-edge spike is censored by the data.  Here we show the
complementary half of the round-88 audit: what the data **do** identify, and
why they identify it uniformly in the cap.

Take three equal bins of the unit interval.  An exponential law with rate `b`
truncated to `[0,1]` has bin probabilities `geomBin r j = r ^ j / (1 + r + r²)`
with `r = exp (-b/3)`; they are geometric, so the *log-convexity defect*

`defect x y z = x * z - y ^ 2`

vanishes identically on the whole single-law family (`defect_geom_eq_zero`).
For the two-component profile *flat bulk + spike* the defect equals
`rho (1 - rho) (1 - r)² / (3 (1 + r + r²))`, which is **strictly positive** and,
once `r ≤ 1/2` (i.e. `b ≥ 3 log 2`), bounded below by `rho (1 - rho) / 21`
independently of `b` (`defect_mix_ge`).  Since the defect is `4`-Lipschitz in
the sup-norm on bin vectors, the mixture stays at sup-distance at least
`rho (1 - rho) / 84` from *every* single-law bin vector
(`single_law_separation`).  This is the formal counterpart of
"`dAICc ≈ -100` at every cap: kernel existence never wavers".

At the same time the observable bin vector is exponentially insensitive to the
steepness (`steepness_valley`): two steepnesses above `B` produce bin vectors
within `4 rho exp (-B/3)` of each other.  Identified: the presence of the
kernel.  Unidentified: how steep it is.

The section `GeneralBins` repeats the whole argument for an arbitrary number
`k ≥ 1` of equal bins: `defect_geomK_eq_zero`, the closed form
`defect_mixK_eq`, the cap-uniform bound `rho (1 - rho) / (8 k)`
(`defect_mixK_ge`) and the separation `rho (1 - rho) / (32 k)`
(`single_law_separationK`).  The evidence for a second component therefore
degrades only linearly in the number of bins, never with the steepness.

Finally `twoComp_role_swap` records the second, exact non-identifiability
direction disclosed in the ledger: swapping the two components together with
the mixing weight leaves every observable unchanged, so no criterion computed
from the bin probabilities can have a unique maximiser.
-/

open EdgeSpikeDefect

open Real





variable {r : ℝ} {j : ℕ}











variable {r rho : ℝ}









variable {rho r r' : ℝ}











/-!
### From three bins to `k` bins

The three-bin computation is not special.  For any number `k ≥ 1` of equal bins
the single-law weights are still geometric, hence still have vanishing second
log-differences, while the flat-plus-spike mixture has defect
`rho (1 - rho) / k · q_j (1 - r)²`.  The margin degrades only like `1/k`.
-/



variable {k j : ℕ} {r rho : ℝ}

lemma geomK_den_pos (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < 1 - r ^ k := by
  have : r ^ k < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  linarith





/-- **Closed form of the `k`-bin defect of the two-component profile.** -/
theorem defect_mixK_eq (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    defect (mixBinK k rho r j) (mixBinK k rho r (j + 1)) (mixBinK k rho r (j + 2)) =
      rho * (1 - rho) / k * (geomBinK k r j * (1 - r) ^ 2) := by
  have hden : (1 : ℝ) - r ^ k ≠ 0 := ne_of_gt (geomK_den_pos hk hr0 hr1)
  have hk0 : (k : ℝ) ≠ 0 := by
    have : 0 < k := hk
    positivity
  unfold defect mixBinK geomBinK
  field_simp
  ring





open EdgeSpikeDefect in
theorem solution(hk : 1 ≤ k) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    rho * (1 - rho) / (8 * k) ≤
      defect (mixBinK k rho r 0) (mixBinK k rho r 1) (mixBinK k rho r 2) := by
  have hrlt : r < 1 := by linarith
  have hden := geomK_den_pos hk hr0 hrlt
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [defect_mixK_eq hk hr0 hrlt]
  have hq0 : (1 : ℝ) / 2 ≤ geomBinK k r 0 := by
    unfold geomBinK
    rw [le_div_iff₀ hden]
    have hrk : (0 : ℝ) ≤ r ^ k := pow_nonneg hr0 k
    simp only [pow_zero, one_mul]
    nlinarith
  have hsq : (1 : ℝ) / 4 ≤ (1 - r) ^ 2 := by nlinarith
  have hprod : (1 : ℝ) / 8 ≤ geomBinK k r 0 * (1 - r) ^ 2 := by nlinarith
  have hcoef : 0 < rho * (1 - rho) / k := div_pos (mul_pos hrho0 (by linarith)) hk0
  have : rho * (1 - rho) / (8 * k) = rho * (1 - rho) / k * (1 / 8) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hprod hcoef.le
