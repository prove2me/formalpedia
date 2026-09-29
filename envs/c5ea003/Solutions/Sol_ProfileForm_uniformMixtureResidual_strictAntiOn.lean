-- Prove2me | solution 1 for ProfileForm.uniformMixtureResidual_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:06:29.736342+00:00
-- url     : https://prove2.me/submissions/2299c519-ab89-4b9b-94e6-410cb4cd7101

-- Sol generated from NumberTheory/ProfileFormHumpThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormHumpThreshold
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak
import Theorems.Thm_ProfileForm_dickmanMixtureBaseline_pos
import Theorems.Thm_ProfileForm_one_div_exp_sub_one_gt
import Theorems.Thm_ProfileForm_one_sub_exp_neg_pos
import Theorems.Thm_ProfileForm_uniformLogResidual_hasDerivAt

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


theorem uniformResidual_pos {b x : ℝ} (hx : 0 < x) :
    0 < powerProfile 1 b x / dickmanMixtureBaseline x := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have hnum : 0 < powerProfile 1 b x := by
    simp only [powerProfile, one_mul]; exact Real.rpow_pos_of_pos h1 _
  exact div_pos hnum (dickmanMixtureBaseline_pos hx)

theorem log_uniformResidual {b x : ℝ} (hx : 0 < x) :
    Real.log (powerProfile 1 b x / dickmanMixtureBaseline x) = uniformLogResidual b x := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have hden : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  rw [powerProfile, dickmanMixtureBaseline, uniformLogResidual, one_mul]
  rw [div_div_eq_mul_div, Real.log_div (by positivity) (ne_of_gt hden),
    Real.log_mul (by positivity) (ne_of_gt hx), Real.log_rpow h1]
  ring






open ProfileForm in
theorem solution{b : ℝ} (hb : 3/2 ≤ b) :
    StrictAntiOn (fun x => powerProfile 1 b x / dickmanMixtureBaseline x) (Ioi (0:ℝ)) := by
  have hlog : StrictAntiOn (uniformLogResidual b) (Ioi (0:ℝ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi _)
      (fun t ht => (uniformLogResidual_hasDerivAt b ht).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    rw [(uniformLogResidual_hasDerivAt b hx0).deriv]
    have hcorr := one_div_exp_sub_one_gt hx0
    have h1 : (0:ℝ) < 1 + x := by linarith
    rcases le_or_gt x 2 with hle | hgt
    · -- small `x`: the exponential correction already beats the algebraic term
      have hb3 : (1:ℝ)/2 ≤ b / (1 + x) := by
        rw [le_div_iff₀ h1]; linarith
      linarith
    · -- large `x`: the algebraic term is itself non-positive
      have halg : 1 / x - b / (1 + x) ≤ 0 := by
        rw [sub_nonpos, div_le_div_iff₀ hx0 h1]
        nlinarith
      have hpos : 0 < 1 / (Real.exp x - 1) := by
        have := exp_sub_one_pos hx0; positivity
      linarith
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hRx : 0 < powerProfile 1 b x / dickmanMixtureBaseline x := uniformResidual_pos hx0
  have hRy : 0 < powerProfile 1 b y / dickmanMixtureBaseline y := uniformResidual_pos hy0
  have hlt := hlog hx hy hxy
  rw [← log_uniformResidual hx0, ← log_uniformResidual hy0] at hlt
  exact (Real.log_lt_log_iff hRy hRx).mp hlt
