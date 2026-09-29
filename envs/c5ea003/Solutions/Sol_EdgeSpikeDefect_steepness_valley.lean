-- Prove2me | solution 1 for EdgeSpikeDefect.steepness_valley
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:49:51.273952+00:00
-- url     : https://prove2.me/submissions/35c0eef6-261a-4d0a-b16f-fa4309713db0

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


lemma geomBin_nonneg (hr : 0 ≤ r) : 0 ≤ geomBin r j :=
  div_nonneg (pow_nonneg hr j) (geom_den_pos hr).le








variable {r rho : ℝ}









variable {rho r r' : ℝ}

lemma geomBin_close (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    geomBin r j ≤ r := by
  have hden := geom_den_pos hr0
  unfold geomBin
  rw [div_le_iff₀ hden]
  have hpow : r ^ j ≤ r := by
    calc r ^ j ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1 hj
      _ = r := pow_one r
  nlinarith [sq_nonneg r, mul_nonneg hr0 hr0]

lemma geomBin_zero_close (hr0 : 0 ≤ r) : |geomBin r 0 - 1| ≤ 2 * r := by
  have hden := geom_den_pos hr0
  have hval : geomBin r 0 - 1 = -((r + r ^ 2) / (1 + r + r ^ 2)) := by
    unfold geomBin
    field_simp
    ring
  rw [hval, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hden]
  nlinarith [sq_nonneg r, mul_nonneg hr0 hr0]









/-!
### From three bins to `k` bins

The three-bin computation is not special.  For any number `k ≥ 1` of equal bins
the single-law weights are still geometric, hence still have vanishing second
log-differences, while the flat-plus-spike mixture has defect
`rho (1 - rho) / k · q_j (1 - r)²`.  The margin degrades only like `1/k`.
-/



variable {k j : ℕ} {r rho : ℝ}











open EdgeSpikeDefect in
theorem solution(hrho0 : 0 ≤ rho) {b b' B : ℝ} (hB : 0 ≤ B)
    (hb : B ≤ b) (hb' : B ≤ b') (j : ℕ) :
    |mixBin rho (exp (-(b / 3))) j - mixBin rho (exp (-(b' / 3))) j| ≤
      4 * rho * exp (-(B / 3)) := by
  set eB := exp (-(B / 3)) with hEdef
  have hEpos : 0 < eB := Real.exp_pos _
  have key : ∀ c : ℝ, B ≤ c →
      |geomBin (exp (-(c / 3))) j - (if j = 0 then (1 : ℝ) else 0)| ≤ 2 * eB := by
    intro c hc
    have hcpos : 0 < exp (-(c / 3)) := Real.exp_pos _
    have hcle : exp (-(c / 3)) ≤ eB := Real.exp_le_exp.mpr (by linarith)
    by_cases hj0 : j = 0
    · rw [if_pos hj0, hj0]
      exact le_trans (geomBin_zero_close hcpos.le) (by linarith)
    · rw [if_neg hj0, sub_zero, abs_of_nonneg (geomBin_nonneg (j := j) hcpos.le)]
      have hle := geomBin_close (r := exp (-(c / 3))) hcpos.le
        (Real.exp_le_one_iff.mpr (by linarith)) (Nat.one_le_iff_ne_zero.mpr hj0)
      linarith
  have k1 := key b hb
  have k2 := key b' hb'
  have htri := abs_sub_le (geomBin (exp (-(b / 3))) j) (if j = 0 then (1 : ℝ) else 0)
    (geomBin (exp (-(b' / 3))) j)
  rw [abs_sub_comm (if j = 0 then (1 : ℝ) else 0) (geomBin (exp (-(b' / 3))) j)] at htri
  have hdiff : |geomBin (exp (-(b / 3))) j - geomBin (exp (-(b' / 3))) j| ≤ 4 * eB := by
    linarith
  have hmix : mixBin rho (exp (-(b / 3))) j - mixBin rho (exp (-(b' / 3))) j =
      rho * (geomBin (exp (-(b / 3))) j - geomBin (exp (-(b' / 3))) j) := by
    unfold mixBin; ring
  rw [hmix, abs_mul, abs_of_nonneg hrho0]
  calc rho * |geomBin (exp (-(b / 3))) j - geomBin (exp (-(b' / 3))) j|
      ≤ rho * (4 * eB) := mul_le_mul_of_nonneg_left hdiff hrho0
    _ = 4 * rho * eB := by ring
