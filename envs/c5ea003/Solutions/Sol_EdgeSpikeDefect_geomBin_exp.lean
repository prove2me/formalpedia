-- Prove2me | solution 1 for EdgeSpikeDefect.geomBin_exp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:48:32.290057+00:00
-- url     : https://prove2.me/submissions/81fb32fe-97c7-4d8a-8616-ef83644d9ff0

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

lemma geom_den_pos (hr : 0 ≤ r) : 0 < 1 + r + r ^ 2 := by nlinarith [sq_nonneg r]










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











open EdgeSpikeDefect in
theorem solution(b : ℝ) (hb : 0 < b) (j : ℕ) :
    geomBin (exp (-(b / 3))) j =
      (exp (-(b * j / 3)) - exp (-(b * (j + 1) / 3))) / (1 - exp (-b)) := by
  set r := exp (-(b / 3)) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ n : ℕ, r ^ n = exp (-(b * n / 3)) := by
    intro n
    rw [hrdef, ← Real.exp_nat_mul]
    ring_nf
  have hcube : r ^ 3 = exp (-b) := by
    rw [hpow 3]; norm_num
  have hsucc : exp (-(b * ((j : ℝ) + 1) / 3)) = r ^ (j + 1) := by
    have := hpow (j + 1)
    push_cast at this
    linarith
  have hden : (1 : ℝ) + r + r ^ 2 ≠ 0 := ne_of_gt (geom_den_pos hrpos.le)
  have hone : (1 : ℝ) - r ≠ 0 := by intro hc; linarith
  have hc3 : (1 : ℝ) - r ^ 3 ≠ 0 := by
    have : r ^ 3 < 1 := pow_lt_one₀ hrpos.le hr1 (by norm_num)
    intro hcon; linarith
  rw [← hpow j, hsucc, ← hcube]
  unfold geomBin
  field_simp
  ring
