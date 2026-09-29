-- Prove2me | solution 1 for MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T07:46:00.989612+00:00
-- url     : https://prove2.me/submissions/6aeb6589-d95c-4644-ad80-8112875811f1

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Variance asymptotics for a stationary sequence with summable autocovariances
-/

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace VarAsympAux

/-- Under strict stationarity all coordinates have the law of `Y 0`. -/
theorem map_eq_of_isStrictlyStationary (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (k : ℕ) :
    P.map (Y k) = P.map (Y 0) := by
  have h := congrArg (Measure.map fun f : ℕ → ℝ => f 0) (hstat k)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun n => hY (n + k)),
    Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun n => hY n)] at h
  simpa [Function.comp_def] using h

/-- Every coordinate of a strictly stationary `L²` sequence is in `L²`. -/
theorem memLp_two_of_isStrictlyStationary (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P)
    (k : ℕ) : MemLp (Y k) 2 P := by
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hY 0).aemeasurable).2 (by simpa using hL2)
  have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by
    rw [map_eq_of_isStrictlyStationary P Y hY hstat k]; exact h0
  simpa using (memLp_map_measure_iff aestronglyMeasurable_id (hY k).aemeasurable).1 hk

/-- Strict stationarity transports products of two coordinates. -/
theorem integral_mul_shift_eq (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (i k : ℕ) :
    ∫ ω, Y i ω * Y (k + i) ω ∂P = ∫ ω, Y 0 ω * Y k ω ∂P := by
  have hg : Measurable fun f : ℕ → ℝ => f 0 * f k :=
    ((measurable_pi_apply 0).mul (measurable_pi_apply k))
  have h1 : ∫ y, (y 0 * y k) ∂(P.map fun ω n => Y (n + i) ω)
      = ∫ y, (y 0 * y k) ∂(P.map fun ω n => Y n ω) := by rw [hstat i]
  rw [integral_map (measurable_pi_lambda _ fun n => hY (n + i)).aemeasurable
      hg.aestronglyMeasurable,
    integral_map (measurable_pi_lambda _ fun n => hY n).aemeasurable
      hg.aestronglyMeasurable] at h1
  simpa [Nat.add_comm] using h1

/-- The autocovariance depends only on the distance between the indices. -/
theorem integral_mul_eq_gamma_dist (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (i j : ℕ) :
    ∫ ω, Y i ω * Y j ω ∂P = ∫ ω, Y 0 ω * Y (Nat.dist i j) ω ∂P := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    calc ∫ ω, Y i ω * Y j ω ∂P = ∫ ω, Y i ω * Y ((j - i) + i) ω ∂P := by
          rw [show (j - i) + i = j by omega]
      _ = ∫ ω, Y 0 ω * Y (j - i) ω ∂P := integral_mul_shift_eq P Y hY hstat i (j - i)
  · rw [Nat.dist_eq_sub_of_le_right h]
    calc ∫ ω, Y i ω * Y j ω ∂P = ∫ ω, Y j ω * Y i ω ∂P := by simp_rw [mul_comm]
      _ = ∫ ω, Y j ω * Y ((i - j) + j) ω ∂P := by rw [show (i - j) + j = i by omega]
      _ = ∫ ω, Y 0 ω * Y (i - j) ω ∂P := integral_mul_shift_eq P Y hY hstat j (i - j)

/-- Expansion of the second moment of the partial sum as a double sum of autocovariances. -/
theorem integral_sq_partialSum_eq (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P)
    (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ ω, Y 0 ω * Y (Nat.dist i j) ω ∂P := by
  have hmem : ∀ i, MemLp (Y i) 2 P := memLp_two_of_isStrictlyStationary P Y hY hstat hL2
  have hint : ∀ i j, Integrable (fun ω => Y i ω * Y j ω) P :=
    fun i j => MemLp.integrable_mul (hmem i) (hmem j)
  have hexp : ∀ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Y i ω * Y j ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  exact Finset.sum_congr rfl fun j _ => integral_mul_eq_gamma_dist P Y hY hstat i j

/-- The combinatorial identity `∑_{i,j<n} γ_{|i-j|} = n γ₀ + 2 ∑_{k<n} (n - (k+1)) γ_{k+1}`. -/
theorem sum_sum_dist_eq (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Nat.dist i j)
      = n * g 0 + 2 * ∑ k ∈ Finset.range n, ((n : ℝ) - (k + 1)) * g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrow : ∑ j ∈ Finset.range n, g (Nat.dist n j) = ∑ k ∈ Finset.range n, g (k + 1) := by
      have h1 : ∀ j ∈ Finset.range n, g (Nat.dist n j) = g (n - j) := by
        intro j hj
        rw [Nat.dist_eq_sub_of_le_right (by simp only [Finset.mem_range] at hj; omega)]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [show n - (n - 1 - j) = j + 1 by omega]
    have hcol : ∑ i ∈ Finset.range n, g (Nat.dist i n) = ∑ k ∈ Finset.range n, g (k + 1) := by
      rw [← hrow]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.dist_comm]
    have hsplit : ∀ i, ∑ j ∈ Finset.range (n + 1), g (Nat.dist i j)
        = (∑ j ∈ Finset.range n, g (Nat.dist i j)) + g (Nat.dist i n) := by
      intro i; rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ih, hcol, Nat.dist_self, hrow]
    have hC : ∑ k ∈ Finset.range (n + 1), (((n : ℝ) + 1) - ((k : ℝ) + 1)) * g (k + 1)
        = ∑ k ∈ Finset.range n, ((n : ℝ) - ((k : ℝ) + 1)) * g (k + 1)
          + ∑ k ∈ Finset.range n, g (k + 1) := by
      rw [Finset.sum_range_succ, show (((n : ℝ) + 1) - ((n : ℝ) + 1)) * g (n + 1) = 0 by ring,
        add_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    push_cast
    rw [hC]
    ring

end VarAsympAux

open VarAsympAux in
/-- **Variance asymptotics.**  For a measurable, strictly stationary `L²` sequence with
summable positive-lag autocovariances, `n⁻¹ E[S_n²]` converges to the asymptotic variance. -/
theorem solution (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P Y)) := by
  set gam : ℕ → ℝ := fun k => ∫ ω, Y 0 ω * Y k ω ∂P with hgam
  have habs : Summable fun k => |gam (k + 1)| := hsum.abs
  set F : ℕ → ℕ → ℝ := fun n k => if k < n then (1 - ((k : ℝ) + 1) / n) * gam (k + 1) else 0
    with hF
  -- the truncated weighted sums are the partial sums of `F n`
  have hFsum : ∀ n : ℕ, ∑' k, F n k
      = ∑ k ∈ Finset.range n, (1 - ((k : ℝ) + 1) / n) * gam (k + 1) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      have hkn : ¬ k < n := by simpa using hk
      simp only [hF, if_neg hkn])]
    exact Finset.sum_congr rfl fun k hk => by
      simp only [hF, if_pos (Finset.mem_range.1 hk)]
  -- pointwise convergence of the weights
  have hpt : ∀ k, Tendsto (fun n => F n k) atTop (𝓝 (gam (k + 1))) := by
    intro k
    have hzero : Tendsto (fun n : ℕ => ((k : ℝ) + 1) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - ((k : ℝ) + 1) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
    have h1 : Tendsto (fun n : ℕ => (1 - ((k : ℝ) + 1) / n) * gam (k + 1)) atTop
        (𝓝 (gam (k + 1))) := by
      simpa using h2.mul (tendsto_const_nhds (x := gam (k + 1)))
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    simp only [hF, if_pos hn]
  -- domination
  have hbound : ∀ n k, ‖F n k‖ ≤ |gam (k + 1)| := by
    intro n k
    by_cases hk : k < n
    · have hnn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
      have hn : (0 : ℝ) < n := by exact_mod_cast hnn
      have hle : ((k : ℝ) + 1) / n ≤ 1 := by
        rw [div_le_one hn]
        exact_mod_cast Nat.succ_le_of_lt hk
      have hge : (0 : ℝ) ≤ ((k : ℝ) + 1) / n := by positivity
      have : |1 - ((k : ℝ) + 1) / n| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      simp only [hF, if_pos hk, Real.norm_eq_abs, abs_mul]
      calc |1 - ((k : ℝ) + 1) / n| * |gam (k + 1)| ≤ 1 * |gam (k + 1)| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |gam (k + 1)| := one_mul _
    · simp only [hF, if_neg hk, norm_zero]
      exact abs_nonneg _
  have hlim : Tendsto (fun n => ∑' k, F n k) atTop (𝓝 (∑' k, gam (k + 1))) :=
    tendsto_tsum_of_dominated_convergence habs hpt (Eventually.of_forall hbound)
  -- assemble
  have hgoal : Tendsto (fun n : ℕ => gam 0 + 2 * ∑' k, F n k) atTop
      (𝓝 (gam 0 + 2 * ∑' k, gam (k + 1))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
  have hvar_eq : seqAsymptoticVariance P Y = gam 0 + 2 * ∑' k, gam (k + 1) := by
    simp only [seqAsymptoticVariance, hgam]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [hvar_eq]
  refine hgoal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ k : ℕ, (1 - ((k : ℝ) + 1) / n) * gam (k + 1)
      = (n : ℝ)⁻¹ * (((n : ℝ) - ((k : ℝ) + 1)) * gam (k + 1)) := by
    intro k
    field_simp
  rw [VarAsympAux.integral_sq_partialSum_eq P Y hY hstat hL2 n, VarAsympAux.sum_sum_dist_eq gam n, hFsum n,
    Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  field_simp

