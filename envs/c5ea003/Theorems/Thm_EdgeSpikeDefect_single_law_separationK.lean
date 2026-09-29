-- Prove2me | Theorems.Thm_EdgeSpikeDefect_single_law_separationK
-- name    : EdgeSpikeDefect.single_law_separationK
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:32:10.206982+00:00
-- url     : https://prove2.me/theorems/29b80335-2670-473f-a228-37d4690eaab0
-- title:
--   `k`-bin single-law exclusion.
-- statement:
--   **`k`-bin single-law exclusion.**  Some bin probability of the mixture
--   differs from that of *any* single law by at least `rho (1 - rho) / (32 k)`.
--
--   ```lean
--   theorem EdgeSpikeDefect.single_law_separationK{r' : ℝ} (hk : 1 ≤ k) (hrho0 : 0 < rho) (hrho1 : rho < 1)
--       (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hr0' : 0 ≤ r') (hr1' : r' < 1) :
--       rho * (1 - rho) / (32 * k) ≤
--         max |mixBinK k rho r 0 - geomBinK k r' 0|
--           (max |mixBinK k rho r 1 - geomBinK k r' 1| |mixBinK k rho r 2 - geomBinK k r' 2|) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeKernelDefect.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeKernelDefect.lean#L420

-- Thm stub generated from MachineLearning/EdgeSpikeKernelDefect.lean
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

theorem EdgeSpikeDefect.single_law_separationK{r' : ℝ} (hk : 1 ≤ k) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hr0' : 0 ≤ r') (hr1' : r' < 1) :
    rho * (1 - rho) / (32 * k) ≤
      max |mixBinK k rho r 0 - geomBinK k r' 0|
        (max |mixBinK k rho r 1 - geomBinK k r' 1| |mixBinK k rho r 2 - geomBinK k r' 2|) := by sorry
