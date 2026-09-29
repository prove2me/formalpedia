-- Prove2me | Definitions.Def_MachineLearning_EdgeSpikeKernelDefect
-- name    : MachineLearning_EdgeSpikeKernelDefect
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:50.106903+00:00
-- url     : https://prove2.me/theorems/2ddddf07-6a88-483a-9c44-73466f276ec3
-- title:
--   Aether Catalog definitions — MachineLearning_EdgeSpikeKernelDefect
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.EdgeSpikeKernelDefect`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/EdgeSpikeKernelDefect.lean by skeleton subtraction
import Mathlib

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

namespace EdgeSpikeDefect

open Real

/-- Bin probability of bin `j` for an exponential law truncated to `[0,1]` and
binned into three equal cells, written in terms of `r = exp (-b/3)`. -/
noncomputable def geomBin (r : ℝ) (j : ℕ) : ℝ := r ^ j / (1 + r + r ^ 2)

/-- Bin probability of the *flat bulk + left-edge spike* profile on three equal
bins: weight `1 - rho` uniform, weight `rho` on the truncated exponential. -/
noncomputable def mixBin (rho r : ℝ) (j : ℕ) : ℝ := (1 - rho) / 3 + rho * geomBin r j

/-- The three-bin log-convexity defect.  It vanishes exactly on geometric
(= single truncated-exponential) bin vectors. -/
def defect (x y z : ℝ) : ℝ := x * z - y ^ 2

section GeomBasic

variable {r : ℝ} {j : ℕ}









end GeomBasic

section Defect

variable {r rho : ℝ}







end Defect

section Valley

variable {rho r r' : ℝ}




end Valley

section RoleSwap

/-- Bin probabilities of a genuine two-component mixture of truncated
exponentials with steepnesses `b₁, b₂` and weight `rho` on the first. -/
noncomputable def twoCompBin (rho b₁ b₂ : ℝ) (j : ℕ) : ℝ :=
  rho * geomBin (exp (-(b₁ / 3))) j + (1 - rho) * geomBin (exp (-(b₂ / 3))) j



end RoleSwap

section GeneralBins

/-!
### From three bins to `k` bins

The three-bin computation is not special.  For any number `k ≥ 1` of equal bins
the single-law weights are still geometric, hence still have vanishing second
log-differences, while the flat-plus-spike mixture has defect
`rho (1 - rho) / k · q_j (1 - r)²`.  The margin degrades only like `1/k`.
-/

/-- Bin `j` of a truncated exponential binned into `k` equal cells, `r = exp (-b/k)`. -/
noncomputable def geomBinK (k : ℕ) (r : ℝ) (j : ℕ) : ℝ := r ^ j * (1 - r) / (1 - r ^ k)

/-- Bin `j` of the flat-bulk plus spike profile on `k` equal cells. -/
noncomputable def mixBinK (k : ℕ) (rho r : ℝ) (j : ℕ) : ℝ :=
  (1 - rho) / k + rho * geomBinK k r j

variable {k j : ℕ} {r rho : ℝ}









end GeneralBins

end EdgeSpikeDefect


