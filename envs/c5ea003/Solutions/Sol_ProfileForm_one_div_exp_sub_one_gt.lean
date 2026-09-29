-- Prove2me | solution 1 for ProfileForm.one_div_exp_sub_one_gt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:39:18.970333+00:00
-- url     : https://prove2.me/submissions/384cba70-be19-44eb-9481-7bf4b1f37001

-- Sol generated from NumberTheory/ProfileFormHumpThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormHumpThreshold
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak
import Theorems.Thm_ProfileForm_exp_lt_pade

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
theorem solution{x : ℝ} (hx : 0 < x) :
    1 / x - 1 / 2 < 1 / (Real.exp x - 1) := by
  have hd : 0 < Real.exp x - 1 := exp_sub_one_pos hx
  rcases lt_or_ge x 2 with hx2 | hx2
  · have hp := exp_lt_pade hx hx2
    have h2x : (0:ℝ) < 2 - x := by linarith
    have heq : (2 + x) / (2 - x) - 1 = 2 * x / (2 - x) := by field_simp; ring
    have hstep : Real.exp x - 1 < 2 * x / (2 - x) := by rw [← heq]; linarith
    have hlt : 1 / (2 * x / (2 - x)) < 1 / (Real.exp x - 1) :=
      one_div_lt_one_div_of_lt hd hstep
    have hEq : 1 / (2 * x / (2 - x)) = 1 / x - 1 / 2 := by
      rw [one_div_div]; field_simp
    linarith [hEq ▸ hlt]
  · have h1 : 1 / x - 1 / 2 ≤ 0 := by
      have : 1 / x ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num) hx2
      linarith
    have h2 : 0 < 1 / (Real.exp x - 1) := by positivity
    linarith
