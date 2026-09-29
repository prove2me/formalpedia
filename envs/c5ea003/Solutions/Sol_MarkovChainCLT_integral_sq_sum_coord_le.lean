-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_sum_coord_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:42:15.839677+00:00
-- url     : https://prove2.me/submissions/5748d39c-6f3a-482b-bd52-1e2e1e14cec6

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_integral_mul_coord_eq
import Theorems.Thm_MarkovChainCLT_abs_integral_mul_iterKernel_le
import Theorems.Thm_MarkovChainCLT_sum_geometric_lag_le
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 4000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * n * ∫ x, (r x) ^ 2 ∂π := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  set S : ℝ := ∫ x, (r x) ^ 2 ∂π with hS
  have hS0 : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  set c : ℕ → ℝ := fun d => ∫ x, r x * (∫ y, r y ∂(iterKernel P d x)) ∂π with hc
  have hcbd : ∀ d, |c d| ≤ (1 / 2 : ℝ) ^ (d / N) * S :=
    fun d => abs_integral_mul_iterKernel_le P π hinv N hN ρ hρ0 hρ hrate r hr Br hBr hmean d
  -- integrability of the pairwise products
  have hprodint : ∀ j k : ℕ,
      Integrable (fun ω : ℕ → X => r (ω (j + 1)) * r (ω (k + 1))) ν := by
    intro j k
    refine ⟨((hr.comp (measurable_pi_apply (j + 1))).mul
      (hr.comp (measurable_pi_apply (k + 1)))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hBr (ω (j + 1)), hBr (ω (k + 1)),
      abs_nonneg (r (ω (j + 1))), abs_nonneg (r (ω (k + 1)))]
  -- each pairwise integral is a covariance at the corresponding lag
  have hterm : ∀ j k : ℕ, ∫ ω, r (ω (j + 1)) * r (ω (k + 1)) ∂ν
      = c (max j k - min j k) := by
    intro j k
    rcases le_total j k with hjk | hjk
    · have hidx : j + 1 + (k - j) = k + 1 := by omega
      have h1 := integral_mul_coord_eq P π hinv r hr Br hBr j (k - j)
      rw [hidx] at h1
      rw [h1, max_eq_right hjk, min_eq_left hjk]
    · have hidx : k + 1 + (j - k) = j + 1 := by omega
      have h1 := integral_mul_coord_eq P π hinv r hr Br hBr k (j - k)
      rw [hidx] at h1
      have h2 : ∫ ω, r (ω (j + 1)) * r (ω (k + 1)) ∂ν
          = ∫ ω, r (ω (k + 1)) * r (ω (j + 1)) ∂ν := by
        refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
        ring
      rw [h2, h1, max_eq_left hjk, min_eq_right hjk]
  -- expand the square
  have hsq : ∀ ω : ℕ → X, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          r (ω (j + 1)) * r (ω (k + 1)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hexp : ∫ ω, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2 ∂ν
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c (max j k - min j k) := by
    rw [integral_congr_ae (ae_of_all _ hsq),
      integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hprodint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finset_sum _ (fun k _ => hprodint j k)]
    exact Finset.sum_congr rfl (fun k _ => hterm j k)
  rw [hexp]
  -- bound the double sum
  have hinner : ∀ j ∈ Finset.range n,
      ∑ k ∈ Finset.range n, c (max j k - min j k) ≤ 4 * N * S := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have h1 : ∑ k ∈ Finset.range n, c (max j k - min j k)
        ≤ ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N) * S := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have := hcbd (max j k - min j k)
      calc c (max j k - min j k) ≤ |c (max j k - min j k)| := le_abs_self _
        _ ≤ (1 / 2 : ℝ) ^ ((max j k - min j k) / N) * S := this
    have h2 : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N) * S
        = (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N)) * S := by
      rw [Finset.sum_mul]
    have h3 := sum_geometric_lag_le N hN n j hjn
    have h4 : (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N)) * S
        ≤ (4 * N) * S := mul_le_mul_of_nonneg_right h3 hS0
    linarith [h1, h2, h4]
  calc ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c (max j k - min j k)
      ≤ ∑ _j ∈ Finset.range n, 4 * N * S := Finset.sum_le_sum hinner
    _ = n * (4 * N * S) := by simp [Finset.sum_const, Finset.card_range]
    _ = 4 * N * n * S := by ring
