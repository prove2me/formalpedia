-- Prove2me | solution 1 for WhichFactorWall.monotoneOn_binEntropy_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:21:32.119236+00:00
-- url     : https://prove2.me/submissions/c22829f5-8242-453a-a06b-cd1e58580950

-- Sol generated from Algebra/WhichFactorWallSqrtLaw.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
import Theorems.Thm_WhichFactorWall_four_mul_sub_le_log_ratio
/-
# The which-factor wall, cycle II: the exact resolution law is a square root

`Algebra.WhichFactorWallInvariant` established that the wall (binary capacity)
determines the class imbalance *Lipschitz-stably* only away from balance, and
that **no** linear inversion constant survives as the imbalance approaches
`1/2` (`no_uniform_inversion_constant`).  That looks like bad news for the
trace battery: the mission brief concluded that "the wall carries almost no
information and should be dropped from the battery report".

This file proves that this conclusion is *wrong*, and replaces it by the exact
law.  The wall is invertible everywhere — uniformly, with no guard at all — but
with a **square-root** modulus of continuity, and the exponent `1/2` is optimal:

* `four_mul_sub_le_log_ratio` — the pointwise derivative bound
  `4 (1/2 - x) ≤ log (1-x) - log x` on `(0, 1/2]`, i.e. `binEntropy` is
  `2`-strongly concave-at-balance in the integrated sense.
* `binEntropy_diff_ge_two_mul_sq` — **Pinsker-type inverse bound**:
  `2 (q - p)² ≤ binEntropy q - binEntropy p` for `0 ≤ p ≤ q ≤ 1/2`.
  This is the sharp global replacement for the (false) linear conjecture.
* `imbalance_sqrt_stability` — **unconditional cross-population stability**:
  if two walls agree within `ε` then the imbalances agree within `√(ε/2)`.
  No guard `η`, no hypothesis beyond `p, q ∈ [0, 1/2]`.
* `binary_wall_sqrt_stability` — the same for two binary statistics on two
  different finite populations.
* `binEntropy_gap_two_sided` — the exact quadratic law at balance:
  `2 t² ≤ log 2 - binEntropy (1/2 - t) ≤ 4 t²`.
* `sqrt_law_sharp` — the exponent `1/2` cannot be improved: for every small `ε`
  there are imbalances whose walls agree within `ε` while the imbalances differ
  by `√ε / 2`.

Consequence for the battery report: a wall value is *never* uninformative; its
resolution is `Θ(ε)` away from balance and `Θ(√ε)` at balance.  A reported wall
should be published together with the resolution its error bar implies.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  A derivative bound with the right behaviour at balance -/



/-! ## 2.  The Pinsker-type inverse bound -/

private lemma hasDerivAt_entropyPlusSq {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun z : ℝ => binEntropy z + 2 * (2⁻¹ - z) ^ 2)
      (log (1 - x) - log x - 4 * (2⁻¹ - x)) x := by
  have h1 : HasDerivAt (fun z : ℝ => (2⁻¹ - z : ℝ)) (-1) x := by
    simpa using (hasDerivAt_const x (2⁻¹ : ℝ)).sub (hasDerivAt_id x)
  have h2 : HasDerivAt (fun z : ℝ => 2 * (2⁻¹ - z : ℝ) ^ 2) (2 * (2 * (2⁻¹ - x) * (-1))) x :=
    ((h1.pow 2).const_mul 2).congr_deriv (by ring)
  have h3 := (Real.hasDerivAt_binEntropy hx0 hx1).add h2
  convert h3 using 1
  ring




/-! ## 3.  Unconditional square-root stability of the wall -/



/-! ## 4.  The exact quadratic law at balance, and optimality of the exponent -/




open WhichFactorWall in
theorem solution:
    MonotoneOn (fun z : ℝ => binEntropy z + 2 * (2⁻¹ - z) ^ 2) (Icc 0 2⁻¹) := by
  have hcont : ContinuousOn (fun z : ℝ => binEntropy z + 2 * (2⁻¹ - z) ^ 2) (Icc 0 2⁻¹) :=
    (Real.binEntropy_continuous.add (by fun_prop)).continuousOn
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 2⁻¹) hcont
  · rw [interior_Icc]
    intro y hy
    simp only [mem_Ioo] at hy
    exact (hasDerivAt_entropyPlusSq (by linarith [hy.1] : y ≠ 0)
      (by intro h; rw [h] at hy; linarith [hy.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    simp only [mem_Ioo] at hy
    rw [(hasDerivAt_entropyPlusSq (by linarith [hy.1] : y ≠ 0)
      (by intro h; rw [h] at hy; linarith [hy.2])).deriv]
    linarith [four_mul_sub_le_log_ratio hy.1 hy.2.le]
