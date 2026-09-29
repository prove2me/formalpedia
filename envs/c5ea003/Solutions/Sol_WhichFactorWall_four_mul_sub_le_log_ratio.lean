-- Prove2me | solution 1 for WhichFactorWall.four_mul_sub_le_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:18:02.635007+00:00
-- url     : https://prove2.me/submissions/c282aa4b-f431-4191-a299-9db7875bc047

-- Sol generated from Algebra/WhichFactorWallSqrtLaw.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
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

private lemma hasDerivAt_psi {y : ℝ} (hy0 : y ≠ 0) (hy1 : (1 : ℝ) - y ≠ 0) :
    HasDerivAt (fun z : ℝ => log (1 - z) - log z + 4 * z - 2) (-(1 - y)⁻¹ - y⁻¹ + 4) y := by
  have h1 : HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) y := by
    simpa using (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
  have h2 : HasDerivAt (fun z : ℝ => log (1 - z)) (-(1 - y)⁻¹) y := by
    have h := (Real.hasDerivAt_log hy1).comp y h1
    simpa [mul_comm] using h
  have h3 := ((h2.sub (Real.hasDerivAt_log hy0)).add ((hasDerivAt_id y).const_mul 4)).sub_const 2
  convert h3 using 1
  ring


/-! ## 2.  The Pinsker-type inverse bound -/





/-! ## 3.  Unconditional square-root stability of the wall -/



/-! ## 4.  The exact quadratic law at balance, and optimality of the exponent -/




open WhichFactorWall in
theorem solution{x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2⁻¹) :
    4 * (2⁻¹ - x) ≤ log (1 - x) - log x := by
  have hanti : AntitoneOn (fun z : ℝ => log (1 - z) - log z + 4 * z - 2) (Icc x 2⁻¹) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x 2⁻¹)
    · intro y hy
      simp only [mem_Icc] at hy
      exact ((hasDerivAt_psi (by linarith [hy.1] : y ≠ 0)
        (by intro h; nlinarith [hy.2])).differentiableAt.continuousAt).continuousWithinAt
    · rw [interior_Icc]
      intro y hy
      simp only [mem_Ioo] at hy
      exact (hasDerivAt_psi (by linarith [hy.1] : y ≠ 0)
        (by intro h; nlinarith [hy.2])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      simp only [mem_Ioo] at hy
      have hy0 : (0 : ℝ) < y := lt_trans hx0 hy.1
      have hy1 : y < 1 := by linarith [hy.2]
      have hne0 : y ≠ 0 := ne_of_gt hy0
      have hne1 : (1 : ℝ) - y ≠ 0 := by intro h; nlinarith
      rw [(hasDerivAt_psi hne0 hne1).deriv]
      have key : -(1 - y)⁻¹ - y⁻¹ + 4 = -((2 * y - 1) ^ 2 / (y * (1 - y))) := by
        field_simp
        ring
      rw [key]
      have hnn : 0 ≤ (2 * y - 1) ^ 2 / (y * (1 - y)) := div_nonneg (sq_nonneg _) (by nlinarith)
      linarith
  have h := hanti (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
  simp only at h
  norm_num at h
  linarith
