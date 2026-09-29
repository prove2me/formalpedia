-- Prove2me | solution 1 for Catalog.Novelty.AttentionScaleThreshold.incrAt_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:19.49005+00:00
-- url     : https://prove2.me/submissions/f37ea8b2-73ae-4028-8909-993fdee4bb3b

-- Sol generated from Novelty/AttentionScaleThreshold.lean
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_AttentionScaleThreshold

/-!
# Hinges, grid resolution, and the scale threshold (NET-67, cycle 2)

This is the second research cycle on the NET-67 measurement.  Cycle 1
(`Novelty.AttentionBudgetIncrement`, `Novelty.AttentionRetentionKnee`) fixed the
two measured budget laws, audited the verdict, and derived the additive law from
a decay rate degrading like `1/log(context)`.  Three questions were left open,
and each gets a theorem here.

**(1) How much does the measured triple actually determine?**  The 1.5B curve is
a *hinge* `max 16 (base + slope·j)`.  `hingeFits_iff` characterises all hinges
through the measured points `16, 16, 18`, and the answer is uncomfortable:
`hingeFits_slope_ge_two` shows the data only force `slope ≥ 2`, and
`hingeFits_alternative` exhibits a genuinely different fit (`base = 12`,
`slope = 3`).  So the advertised `+2` is a **lower bound**, not a measurement.
`hinge_prediction_discriminates` shows the two fits separate at the very next
octave (`20` versus `21` keys at `4096`), which is exactly the experiment to run.

**(2) Why did NET-66 read `20` where NET-67 reads `18`?**  Because a knee read
on a coarse grid is the least *grid point* above the true knee.  `kneeMul` is
the grid-restricted knee and `kneeMul_bounds` proves the two-sided estimate
`knee ≤ kneeMul < knee + d`.  `coarse_grid_reads_twenty` realises the NET-66/67
discrepancy exactly: a profile whose true knee is `18` is read as `20` on the
spacing-`4` grid, and the error is provably below the spacing.

**(3) Does the halving extrapolate to 7B?**  Cycle 1 calibrated the peakedness
of the two models to `λ₀ = 1` and `λ₀ = 2` at parameter counts `0.5B` and
`1.5B`, i.e. `λ₀(N) = (2N)^θ` with `θ = log 2 / log 3`.  The induced increment
law `incrAt N = 4·(2N)^(-θ)` reproduces both measurements
(`incrAt_half`, `incrAt_three_halves`), is strictly decreasing
(`incrAt_strictAntiOn`), and has an **exact closed-form threshold**:
`incrAt N < 1 ↔ 4.5 < N` (`incrAt_lt_one_iff`).  Hence
`scale_threshold_four_point_five`: *a model above 4.5B parameters needs less
than one extra key per context doubling* — its attention budget is essentially
context-free.  For the proposed 7B cell the prediction is bracketed exactly:
`1/2 < incrAt 7 < 1` (`prediction_7B`).
-/

open Catalog.Novelty.AttentionScaleThreshold

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. Hinges: what the measured triple does and does not determine -/












/-! ### 2. Grid resolution: why a coarse sweep over-reads the knee -/






/-! ### 3. The scale exponent and the context-free threshold -/


theorem theta_pos : 0 < theta :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- The defining property of the exponent: `3^θ = 2`. -/
theorem three_rpow_theta : (3 : ℝ) ^ theta = 2 := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), theta, mul_div_assoc']
  rw [mul_comm, mul_div_assoc, div_self hlog3, mul_one]
  exact Real.exp_log (by norm_num)

/-- Powers of `3` are sent to powers of `2`. -/
theorem three_pow_rpow_theta (n : ℕ) : ((3 : ℝ) ^ n) ^ theta = 2 ^ n := by
  induction n with
  | zero => simp [Real.one_rpow]
  | succ m ih =>
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
      rw [pow_succ, Real.mul_rpow h3 (by norm_num), ih, three_rpow_theta, pow_succ]






/-- The increment law is strictly decreasing in model size. -/
theorem incrAt_strictAntiOn : StrictAntiOn incrAt (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < 2 * a := by simp only [Set.mem_Ioi] at ha; linarith
  have hlt : (2 : ℝ) * a < 2 * b := by linarith
  have h := Real.rpow_lt_rpow_of_neg ha' hlt (neg_neg_iff_pos.2 theta_pos)
  simp only [incrAt]
  linarith

/-- The exact threshold value: at `4.5B` parameters the predicted increment is
exactly one key per doubling. -/
theorem incrAt_threshold : incrAt 4.5 = 1 := by
  have h9 : (2 : ℝ) * 4.5 = 3 ^ 2 := by norm_num
  have hpow : ((3 : ℝ) ^ (2 : ℕ)) ^ theta = 2 ^ (2 : ℕ) := three_pow_rpow_theta 2
  rw [incrAt, h9, Real.rpow_neg (by positivity), hpow]
  norm_num







open Catalog.Novelty.AttentionScaleThreshold in
theorem solution{N : ℝ} (hN : 0 < N) : incrAt N < 1 ↔ 4.5 < N := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq, incrAt_threshold] at h; linarith
    · have := incrAt_strictAntiOn (Set.mem_Ioi.2 hN) (Set.mem_Ioi.2 (by norm_num)) hlt
      rw [incrAt_threshold] at this
      linarith
  · intro h
    have := incrAt_strictAntiOn (Set.mem_Ioi.2 (by norm_num : (0:ℝ) < 4.5))
      (Set.mem_Ioi.2 hN) h
    rw [incrAt_threshold] at this
    linarith
