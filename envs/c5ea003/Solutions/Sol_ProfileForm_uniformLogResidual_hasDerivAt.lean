-- Prove2me | solution 1 for ProfileForm.uniformLogResidual_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:59:44.22088+00:00
-- url     : https://prove2.me/submissions/17a75829-26e4-4da1-80db-2d871a43dcfe

-- Sol generated from NumberTheory/ProfileFormHumpThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormHumpThreshold
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak
import Theorems.Thm_ProfileForm_one_sub_exp_neg_pos

/-!
# Profile form IX: a critical exponent for the mixture hump

`ProfileFormUniformMixturePeak` proved that the residual of the power law
`T(x) = (1+x)^{-b}` against the uniform Dickman surrogate
`M(x) = (1 - e^{-x})/x` really does hump, for the measured exponent
`b = 11/10`, at `x ≈ 10`.  `ProfileFormHumpLocation` then explained the location
via the exact maximiser `x* = 1/(b-1)` of the elementary factor
`x (1+x)^{-b}`.

Both results leave open whether the hump is a *universal* feature of this
profile/baseline pair.  It is not.  The exact logarithmic derivative is

  `d/dx log (T/M)(x) = 1/x - b/(1+x) - 1/(e^x - 1)`,

so the hump is a competition between the algebraic term `1/x - b/(1+x)`, which
is positive up to `x* = 1/(b-1)`, and the exponential correction `1/(e^x - 1)`,
which is large exactly where `x` is small.  As `b` increases, `x*` shrinks into
the region where the correction dominates and the hump is destroyed.

Here we prove the destruction side rigorously:

* `exp_lt_pade` — the Padé bound `e^x < (2+x)/(2-x)` on `(0,2)`;
* `one_div_exp_sub_one_gt` — hence `1/x - 1/2 < 1/(e^x - 1)` for all `x > 0`;
* `uniformMixtureResidual_strictAntiOn` — **for every `b ≥ 3/2` the residual
  `T/M` is strictly decreasing on all of `(0,∞)`: no hump anywhere**;
* `uniform_hump_regime_bracket` — combined with the proved hump at `b = 11/10`,
  the humping regime is bracketed: it holds at `11/10` and fails from `3/2` on,
  so a critical exponent lies in `(11/10, 3/2)`.  Numerically it is
  `b_c ≈ 1.1605`, and the reported bootstrap interval `[0.991, 1.218]` straddles
  it — a second, independent way in which the experiment does not settle the
  qualitative shape.

The constant `3/2` is exactly what the two elementary bounds give: the argument
needs `1/(b-1) ≤ 2 ≤ 2b - 1`, i.e. `2b² - 3b ≥ 0`.
-/

open ProfileForm

open Set Filter Topology


theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := Real.add_one_lt_exp (x := x) (ne_of_gt hx)
  linarith


/-! ### The log-residual and its derivative -/









open ProfileForm in
theorem solution(b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (uniformLogResidual b)
      (1 / x - b / (1 + x) - 1 / (Real.exp x - 1)) x := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have hden : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  have hd : 0 < Real.exp x - 1 := exp_sub_one_pos hx
  have hL1 : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx)
  have hL2 : HasDerivAt (fun t : ℝ => b * Real.log (1 + t)) (b * (1 / (1 + x))) x := by
    have hg : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have := (Real.hasDerivAt_log (ne_of_gt h1)).comp x hg
    simpa [one_div] using this.const_mul b
  have hL3 : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-t)))
      (Real.exp (-x) / (1 - Real.exp (-x))) x := by
    have hg : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := by
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-x)) x := by
        simpa using (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      simpa using h2.const_sub 1
    have := (Real.hasDerivAt_log (ne_of_gt hden)).comp x hg
    simpa [div_eq_mul_inv, mul_comm] using this
  have hcorr : Real.exp (-x) / (1 - Real.exp (-x)) = 1 / (Real.exp x - 1) := by
    have h11 : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt hd)]
    linear_combination h11
  have := (hL1.sub hL2).sub hL3
  rw [hcorr] at this
  convert this using 1
  ring
