-- Prove2me | solution 1 for Ising.peierls_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:21:48.968703+00:00
-- url     : https://prove2.me/submissions/af53921a-92e8-4a16-92e0-604f3714b104

-- Sol generated from Applications/IsingModel/Peierls.lean
import Mathlib
import Definitions.Def_Applications_IsingModel_Peierls

/-!
# 2D Ising Model: The Peierls Argument (analytic core)

The Peierls argument proves spontaneous magnetization of the 2D Ising model at
low temperature by bounding the probability that the spin at the origin is flipped
against the boundary condition.  That probability is dominated by a sum over
*contours* (Peierls contours) `γ` enclosing the origin, each weighted by
`e^{-2β|γ|}`.  The number of contours of length `L` enclosing a fixed site is at
most `L · 3^{L}`, so the misalignment probability is dominated by the
**Peierls majorant**
`P(β) = ∑_{L} L · (3 e^{-2β})^{L}`.
When `P(β) < 1/2`, the origin spin keeps its boundary value with probability
`> 1/2`, giving spontaneous magnetization.  Here we formalize the analytic heart:
convergence of `P(β)`, its closed form, and the existence of a low-temperature
threshold `β₀` beyond which `P(β) < 1/2`.

-- !-- Lab Notes -- !--
* **Hypothesis.** The contour majorant `P(β) = ∑_L L (3e^{-2β})^L` converges for
  `3 e^{-2β} < 1` and tends to `0` as `β → ∞`, so a Peierls threshold exists.
* **Experiment.** Set `x = 3 e^{-2β}`. Use `tsum_coe_mul_geometric_of_norm_lt_one`
  to get `∑ L·x^L = x/(1-x)^2`, and `summable_pow_mul_geometric_of_norm_lt_one`
  (with `k = 1`) for convergence. For the threshold pick `β₀ = ½ log 12`, so
  `x ≤ 1/4`, whence `2x < (1-x)^2 ⇔ 0 < 1 - 4x + x^2`, giving `P < 1/2`.
* **Analysis.** Survives. The geometric closed form is exact; the threshold is a
  concrete, checkable inequality reducing to `0 < 1 - 4x + x^2` for `x ≤ 1/4`.
  The full lattice-probabilistic statement (defining contours and the Peierls
  coupling) is *true but hard* and is left to the geometry layer — the analytic
  obstruction (this series) is what controls the phase transition, and it is
  fully discharged here with 0 sorries.
* **Critique.** Not trivial: requires `Summable`/`tsum` machinery, `norm`
  estimates and a genuine inequality chain (`div_lt_iff₀`, `nlinarith`). The
  threshold is existential but *witnessed* (`β₀ = ½ log 12`), avoiding vacuity.
* **Synthesis.** Low temperature ⇒ `P(β) < 1/2` ⇒ Peierls criterion for
  spontaneous magnetization holds.
-/

open Ising

open Real


/-- The contour activity `x = 3 e^{-2β}` is positive. -/
lemma activity_pos (β : ℝ) : 0 < 3 * Real.exp (-2 * β) := by positivity

/-- For `β > ½ log 3` the contour activity is `< 1`. -/
lemma activity_lt_one {β : ℝ} (hβ : Real.log 3 / 2 < β) :
    3 * Real.exp (-2 * β) < 1 := by
  have h1 : -2 * β < -Real.log 3 := by linarith
  have h2 : Real.exp (-2 * β) < Real.exp (-Real.log 3) := Real.exp_lt_exp.mpr h1
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 3)] at h2
  have : (3:ℝ)⁻¹ = 1 / 3 := by norm_num
  rw [this] at h2; linarith

/-- The activity has norm `< 1` for `β > ½ log 3`. -/
lemma norm_activity {β : ℝ} (hβ : Real.log 3 / 2 < β) :
    ‖(3 * Real.exp (-2 * β))‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (activity_pos β)]; exact activity_lt_one hβ


/-- **Closed form of the Peierls majorant.** For `β > ½ log 3`,
`P(β) = x / (1 - x)^2` with `x = 3 e^{-2β}`. -/
theorem peierls_closed_form {β : ℝ} (hβ : Real.log 3 / 2 < β) :
    peierlsBound β =
      (3 * Real.exp (-2 * β)) / (1 - 3 * Real.exp (-2 * β)) ^ 2 := by
  rw [peierlsBound]; exact tsum_coe_mul_geometric_of_norm_lt_one (norm_activity hβ)




open Ising in
theorem solution:
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → peierlsBound β < 1 / 2 := by
  refine ⟨Real.log 12 / 2, ?_, ?_⟩
  · exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  · intro β hβ
    have hlog : Real.log 3 < Real.log 12 := Real.log_lt_log (by norm_num) (by norm_num)
    have hβ3 : Real.log 3 / 2 < β := by linarith
    rw [peierls_closed_form hβ3]
    have hxpos : 0 < 3 * Real.exp (-2 * β) := activity_pos β
    have e12 : Real.exp (-Real.log 12) = 1 / 12 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hexp : Real.exp (-2 * β) ≤ 1 / 12 := by
      have h := Real.exp_le_exp.mpr (show -2 * β ≤ -Real.log 12 by linarith)
      rwa [e12] at h
    have hxle : 3 * Real.exp (-2 * β) ≤ 1 / 4 := by linarith
    have hden : 0 < (1 - 3 * Real.exp (-2 * β)) ^ 2 := pow_pos (by linarith) 2
    rw [div_lt_iff₀ hden]
    nlinarith [hxpos, hxle]
