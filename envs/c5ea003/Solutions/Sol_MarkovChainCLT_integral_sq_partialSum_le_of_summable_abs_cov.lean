-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_partialSum_le_of_summable_abs_cov
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T12:35:42.04886+00:00
-- url     : https://prove2.me/submissions/8ae56164-1e65-46af-9f33-060eed193e41

import Definitions.Def_MixingCoefficients
import Mathlib.Data.Nat.Dist

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under strict stationarity all coordinates have the law of `Y 0`. -/
private theorem map_eq_of_isStrictlyStationary (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (k : ℕ) :
    P.map (Y k) = P.map (Y 0) := by
  have h := congrArg (Measure.map fun f : ℕ → ℝ => f 0) (hstat k)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun n => hY (n + k)),
    Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun n => hY n)] at h
  simpa [Function.comp_def] using h

/-- Every coordinate of a strictly stationary `L²` sequence is in `L²`. -/
private theorem memLp_two_of_isStrictlyStationary (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P)
    (k : ℕ) : MemLp (Y k) 2 P := by
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hY 0).aemeasurable).2 (by simpa using hL2)
  have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by
    rw [map_eq_of_isStrictlyStationary P Y hY hstat k]; exact h0
  simpa using (memLp_map_measure_iff aestronglyMeasurable_id (hY k).aemeasurable).1 hk

/-- Strict stationarity transports products of two coordinates. -/
private theorem integral_mul_shift_eq (P : Measure Ω) (Y : ℕ → Ω → ℝ)
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
private theorem integral_mul_eq_gamma_dist (P : Measure Ω) (Y : ℕ → Ω → ℝ)
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
private theorem integral_sq_partialSum_eq (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
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
private theorem sum_sum_dist_eq (g : ℕ → ℝ) (n : ℕ) :
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

/-- **Uniform linear bound on `E[S_n²]`.**  For a measurable, strictly stationary `L²`
sequence with absolutely summable positive-lag autocovariances, the second moment of the
partial sums grows at most linearly, with an explicit constant. -/
theorem solution (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      ≤ (n : ℝ) * ((∫ ω, Y 0 ω ^ 2 ∂P)
          + 2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) := by
  set g : ℕ → ℝ := fun k => ∫ ω, Y 0 ω * Y k ω ∂P with hg
  have hgamma0 : g 0 = ∫ ω, Y 0 ω ^ 2 ∂P := by
    simp only [hg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have hexp : ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = n * g 0 + 2 * ∑ k ∈ Finset.range n, ((n : ℝ) - (k + 1)) * g (k + 1) := by
    rw [integral_sq_partialSum_eq P Y hY hstat hL2 n]
    exact sum_sum_dist_eq g n
  have hterm : ∀ k ∈ Finset.range n, ((n : ℝ) - (k + 1)) * g (k + 1) ≤ (n : ℝ) * |g (k + 1)| := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by
      have : k + 1 ≤ n := Finset.mem_range.1 hk
      exact_mod_cast this
    have h1 : ((n : ℝ) - (k + 1)) * g (k + 1) ≤ ((n : ℝ) - (k + 1)) * |g (k + 1)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have h2 : ((n : ℝ) - (k + 1)) * |g (k + 1)| ≤ (n : ℝ) * |g (k + 1)| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hpartial : ∑ k ∈ Finset.range n, ((n : ℝ) - (k + 1)) * g (k + 1)
      ≤ (n : ℝ) * ∑' k : ℕ, |g (k + 1)| := by
    calc ∑ k ∈ Finset.range n, ((n : ℝ) - (k + 1)) * g (k + 1)
        ≤ ∑ k ∈ Finset.range n, (n : ℝ) * |g (k + 1)| := Finset.sum_le_sum hterm
      _ = (n : ℝ) * ∑ k ∈ Finset.range n, |g (k + 1)| := by rw [Finset.mul_sum]
      _ ≤ (n : ℝ) * ∑' k : ℕ, |g (k + 1)| :=
          mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun k _ => abs_nonneg _)
            (Nat.cast_nonneg n)
  rw [hexp, hgamma0]
  nlinarith [hpartial, Nat.cast_nonneg (α := ℝ) n]

