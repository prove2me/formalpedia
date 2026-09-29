-- Prove2me | Definitions.Def_Applications_AdjacentSumPolytopes_DominantGrowth
-- name    : Applications_AdjacentSumPolytopes_DominantGrowth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:23:25.250326+00:00
-- url     : https://prove2.me/theorems/2cc9a393-eb08-4107-8edc-b1f6b938b232
-- title:
--   Aether Catalog definitions — Applications_AdjacentSumPolytopes_DominantGrowth
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AdjacentSumPolytopes.DominantGrowth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AdjacentSumPolytopes/DominantGrowth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth

/-!
# The dominant growth rate of the adjacent-sum model

The bounds of `Applications.AdjacentSumPolytopes.Growth` bracket the counts between two
exponentials but do not say that a growth *rate* exists.  Here we prove that it does,
by a Fekete (subadditivity) argument applied to the diagonal counts

`diagCount s n = (adjMat s ^ n) 0 0 = #{open points of length n+1 with x₀ = xₙ = 0}`,

which are supermultiplicative because concatenation of two loops at the state `0` is a
loop at `0`.  The resulting limit

`λ_s = exp (lim_{n} (log diagCount s n)/n)`

is the reciprocal of the dominant real pole of the shared characteristic denominator,
and we show `⌊s/2⌋ + 1 ≤ λ_s ≤ s + 1` (in logarithmic form).

-- !-- Lab Notes -- !--
* **Hypothesis.** Loops at the state `0` are supermultiplicative, so Fekete's lemma
  applies and the exponential growth rate exists; the block bounds of the previous file
  bracket it.
* **Experiment.** `diagCount 2 n = 1, 1, 3, 6, 14, 31, 70, 157, ...` and the ratios
  `1, 3, 2, 2.33, 2.21, 2.26, 2.24, ...` oscillate towards the dominant root `≈ 2.2470`
  of `x³ − 2x² − x + 1`, comfortably inside `[2, 3]`.  For `s = 3`:
  `1, 1, 4, 10, 30, 85, 246, 707` with ratios approaching `≈ 2.87 ∈ [2, 4]`.
* **Analysis.** The `Subadditive` machinery of Mathlib needs `BddBelow` of `u n / n`
  where `u n = − log (diagCount s n)`; the upper block bound supplies exactly that.
  The lower bound on the limit needs a shifted subsequence, since `diagCount s 0 = 1`
  carries no information.
* **Critique.** The statement is not vacuous: `diagCount s n ≥ 1` is proved (the all-zero
  point is always admissible), so all logarithms are of positive numbers, and for
  `s ≥ 2` the limit is at least `log 2 > 0`, i.e. genuinely exponential growth.
-/

namespace AdjSum

open Finset Matrix Filter Topology

/-! ## A Fekete-type growth lemma -/



/-! ## The diagonal loop counts -/

/-- `diagCount s n` is the number of open adjacent-sum points of length `n + 1` whose
first and last coordinates are `0`; equivalently the `(0,0)` entry of the `n`-th power
of the transfer matrix. -/
def diagCount (s n : ℕ) : ℕ := (adjMat s ^ n) 0 0







/-! ## Existence of the dominant growth rate -/



end AdjSum


