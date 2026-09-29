-- Prove2me | solution 1 for EdgeSpikeDefect.single_law_separationK
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:49:50.775493+00:00
-- url     : https://prove2.me/submissions/2f6fe7ae-f407-4a00-8363-8c58010b0d94

-- Sol generated from MachineLearning/EdgeSpikeKernelDefect.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeKernelDefect
import Theorems.Thm_EdgeSpikeDefect_defect_mixK_ge

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





/-- The defect is `4`-Lipschitz in the sup-norm on `[0,1]`-valued bin vectors. -/
theorem defect_lipschitz {x y z x' y' z' e : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx' : 0 ≤ x') (hx1' : x' ≤ 1) (hy' : 0 ≤ y') (hy1' : y' ≤ 1)
    (hdx : |x - x'| ≤ e) (hdy : |y - y'| ≤ e) (hdz : |z - z'| ≤ e) :
    |defect x y z - defect x' y' z'| ≤ 4 * e := by
  have hxx := abs_le.mp hdx
  have hyy := abs_le.mp hdy
  have hzz := abs_le.mp hdz
  have he : 0 ≤ e := le_trans (abs_nonneg _) hdx
  unfold defect
  rw [abs_le]
  constructor <;> nlinarith [hxx.1, hxx.2, hyy.1, hyy.2, hzz.1, hzz.2]




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

lemma geomBinK_nonneg (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 ≤ geomBinK k r j := by
  unfold geomBinK
  exact div_nonneg (mul_nonneg (pow_nonneg hr0 j) (by linarith))
    (geomK_den_pos hk hr0 hr1).le

lemma geomBinK_le_one (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hr1 : r < 1) : geomBinK k r j ≤ 1 := by
  have hden := geomK_den_pos hk hr0 hr1
  have hrk : r ^ k ≤ r := by
    calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hk
      _ = r := pow_one r
  have hnum : r ^ j * (1 - r) ≤ 1 - r ^ k := by
    have h1 : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1.le
    nlinarith
  unfold geomBinK
  rw [div_le_one hden]
  exact hnum


/-- **Every single law has vanishing second log-difference, for every `k`.** -/
theorem defect_geomK_eq_zero (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    defect (geomBinK k r j) (geomBinK k r (j + 1)) (geomBinK k r (j + 2)) = 0 := by
  have hden : (1 : ℝ) - r ^ k ≠ 0 := ne_of_gt (geomK_den_pos hk hr0 hr1)
  unfold defect geomBinK
  field_simp
  ring






open EdgeSpikeDefect in
theorem solution{r' : ℝ} (hk : 1 ≤ k) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hr0' : 0 ≤ r') (hr1' : r' < 1) :
    rho * (1 - rho) / (32 * k) ≤
      max |mixBinK k rho r 0 - geomBinK k r' 0|
        (max |mixBinK k rho r 1 - geomBinK k r' 1| |mixBinK k rho r 2 - geomBinK k r' 2|) := by
  have hrlt : r < 1 := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set e := max |mixBinK k rho r 0 - geomBinK k r' 0|
      (max |mixBinK k rho r 1 - geomBinK k r' 1| |mixBinK k rho r 2 - geomBinK k r' 2|)
    with hedef
  have h0 : |mixBinK k rho r 0 - geomBinK k r' 0| ≤ e := le_max_left _ _
  have h1 : |mixBinK k rho r 1 - geomBinK k r' 1| ≤ e :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : |mixBinK k rho r 2 - geomBinK k r' 2| ≤ e :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hmixnn : ∀ i : ℕ, 0 ≤ mixBinK k rho r i := by
    intro i
    unfold mixBinK
    have := geomBinK_nonneg (k := k) (j := i) hk hr0 hrlt
    have : 0 ≤ (1 - rho) / k := div_nonneg (by linarith) hk0.le
    positivity
  have hmixle : ∀ i : ℕ, mixBinK k rho r i ≤ 1 := by
    intro i
    unfold mixBinK
    have hg := geomBinK_le_one (k := k) (j := i) hk hr0 hrlt
    have hka : (1 - rho) / k ≤ 1 - rho := by
      rw [div_le_iff₀ hk0]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    nlinarith
  have hlip := defect_lipschitz
    (hmixnn 0) (hmixle 0) (hmixnn 1) (hmixle 1) (hmixnn 2) (hmixle 2)
    (geomBinK_nonneg (k := k) (j := 0) hk hr0' hr1')
    (geomBinK_le_one (k := k) (j := 0) hk hr0' hr1')
    (geomBinK_nonneg (k := k) (j := 1) hk hr0' hr1')
    (geomBinK_le_one (k := k) (j := 1) hk hr0' hr1')
    h0 h1 h2
  have hzero : defect (geomBinK k r' 0) (geomBinK k r' 1) (geomBinK k r' 2) = 0 := by
    have := defect_geomK_eq_zero (k := k) (j := 0) hk hr0' hr1'
    simpa using this
  rw [hzero, sub_zero] at hlip
  have hlow := defect_mixK_ge hk hrho0 hrho1 hr0 hr1
  have hpos : 0 < defect (mixBinK k rho r 0) (mixBinK k rho r 1) (mixBinK k rho r 2) := by
    have hc : 0 < rho * (1 - rho) / (8 * k) :=
      div_pos (mul_pos hrho0 (by linarith)) (by linarith)
    linarith
  rw [abs_of_pos hpos] at hlip
  have h8 : rho * (1 - rho) / (8 * k) ≤ 4 * e := le_trans hlow hlip
  have hmul := (div_le_iff₀ (show (0 : ℝ) < 8 * k by linarith)).mp h8
  rw [div_le_iff₀ (show (0 : ℝ) < 32 * k by linarith)]
  linarith
