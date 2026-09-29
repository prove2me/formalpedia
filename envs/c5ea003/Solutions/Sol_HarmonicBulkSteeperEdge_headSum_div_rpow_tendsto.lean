-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headSum_div_rpow_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:38.892222+00:00
-- url     : https://prove2.me/submissions/c396d4f2-0fdb-4329-9256-8f4b4068899d

-- Sol generated from Probability/SubHarmonicSaturationRate.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
import Theorems.Thm_HarmonicBulkSteeperEdge_headSum_sandwich_lower
import Theorems.Thm_HarmonicBulkSteeperEdge_headSum_sandwich_upper
/-
  # The saturation rate below the harmonic exponent

  `Probability.HarmonicBulkSteeperEdge` proves the *saturation dichotomy* for the head
  statistic of a discrete power-law kernel `k ↦ k ^ (-a)` on `{1, …, n}`: the head mass of
  a fixed window `{1, …, m}` tends to a positive limit iff `a > 1`, and collapses to `0`
  for `a ≤ 1`.  `Probability.HarmonicSaturationRate` pins the *rate* of that collapse at
  the harmonic exponent `a = 1`, where it is logarithmic: `headMass 1 n m · log n → H(m)`.

  This file closes the remaining half of the rate question — the *sub-harmonic* regime
  `0 ≤ a < 1`, where the collapse is polynomial rather than logarithmic:

  * `headSum_sandwich_lower` / `headSum_sandwich_upper` — the non-asymptotic two-sided
    bound `((n+1)^{1-a} - 1)/(1-a) ≤ headSum a n ≤ 1 + (n^{1-a} - 1)/(1-a)`, obtained by
    monotone sum/integral comparison for the antitone kernel `x ↦ x^{-a}`.
  * `headSum_div_rpow_tendsto` — consequently `headSum a n / n^{1-a} → 1/(1-a)`.
  * `headMass_mul_rpow_tendsto` — the rate itself:
    `headMass a n m · n^{1-a} → (1-a) · headSum a m`.
  * `headMass_doubling_ratio_tendsto` — the calibration corollary: *doubling* the
    truncation multiplies the dial asymptotically by `2^{a-1}`.  (Contrast the harmonic
    case, where doubling is asymptotically neutral and *squaring* halves the dial.)

  Together with `HarmonicSaturationRate` this fixes the truncation artefact for every
  exponent `a ≤ 1`, so recorded dials taken at different truncations become comparable:
  at `a < 1` the level scales like `n^{a-1}`, at `a = 1` like `1 / log n`, and only for
  `a > 1` does it saturate.
-/

open Filter Topology

open HarmonicBulkSteeperEdge

/-! ## The kernel is antitone on the positive reals -/


/-! ## Non-asymptotic sandwich for the truncated sum -/



/-! ## The polynomial rate -/





open HarmonicBulkSteeperEdge in
theorem solution{a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => headSum a n / (n : ℝ) ^ (1 - a)) atTop (𝓝 (1 / (1 - a))) := by
  set t : ℝ := 1 - a with hti
  have ht : 0 < t := by rw [hti]; linarith
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ t)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ t) atTop atTop :=
      (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp h1
  have hone : Tendsto (fun n : ℕ => (1 + ((n : ℝ))⁻¹) ^ t) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 + ((n : ℝ))⁻¹) atTop (𝓝 1) := by
      have := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa using this.const_add 1
    have hc : ContinuousAt (fun x : ℝ => x ^ t) 1 :=
      Real.continuousAt_rpow_const 1 t (Or.inl one_ne_zero)
    simpa using hc.tendsto.comp h0
  have hlow :
      Tendsto (fun n : ℕ => ((1 + ((n : ℝ))⁻¹) ^ t - ((n : ℝ) ^ t)⁻¹) / t) atTop (𝓝 (1 / t)) := by
    have := (hone.sub hinv).div_const t
    simpa using this
  have hup :
      Tendsto (fun n : ℕ => ((n : ℝ) ^ t)⁻¹ + (1 - ((n : ℝ) ^ t)⁻¹) / t) atTop (𝓝 (1 / t)) := by
    have := hinv.add
      (((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hinv).div_const t)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnt : (0 : ℝ) < (n : ℝ) ^ t := Real.rpow_pos_of_pos hn0 t
    have hrat : ((n : ℝ) + 1) ^ t / (n : ℝ) ^ t = (1 + ((n : ℝ))⁻¹) ^ t := by
      rw [← Real.div_rpow (by linarith) hn0.le]
      congr 1
      field_simp
    have hL := headSum_sandwich_lower ha ha1 n
    rw [← hti] at hL
    have key : ((1 + ((n : ℝ))⁻¹) ^ t - ((n : ℝ) ^ t)⁻¹) / t
        = ((((n : ℝ) + 1) ^ t - 1) / t) / (n : ℝ) ^ t := by
      rw [← hrat]; field_simp
    rw [key]
    gcongr
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnt : (0 : ℝ) < (n : ℝ) ^ t := Real.rpow_pos_of_pos hn0 t
    have hU := headSum_sandwich_upper ha ha1 hn
    rw [← hti] at hU
    have key : ((n : ℝ) ^ t)⁻¹ + (1 - ((n : ℝ) ^ t)⁻¹) / t
        = (1 + (((n : ℝ) ^ t - 1) / t)) / (n : ℝ) ^ t := by
      field_simp
    rw [key]
    gcongr
