-- Prove2me | solution 1 for MarkovChainCLT.integrable_sq_scaled_sampleAvg
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:34:09.454125+00:00
-- url     : https://prove2.me/submissions/8619895f-1770-461e-9bc1-83d36f8ed650

import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_ProbabilityTheory_integrable_of_integrable_sq
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π) (n : ℕ) :
    Integrable (fun ω => (Real.sqrt n * (sampleAvg r n ω - ∫ x, r x ∂π)) ^ 2)
      (chainMeasure P π) := by
  classical
  set c : ℝ := ∫ x, r x ∂π with hc
  set g : X → ℝ := fun x => r x - c with hg
  have hgm : Measurable g := hr.sub measurable_const
  have hrint : Integrable r π := ProbabilityTheory.integrable_of_integrable_sq π r hr hL2
  have hgsq : Integrable (fun x => (g x) ^ 2) π := by
    have hexp : ∀ x, (g x) ^ 2 = (r x) ^ 2 - 2 * c * r x + c ^ 2 := by
      intro x; rw [hg]; ring
    have h : Integrable (fun x => (r x) ^ 2 - 2 * c * r x + c ^ 2) π :=
      (hL2.sub (hrint.const_mul (2 * c))).add (integrable_const _)
    exact h.congr (by filter_upwards with x; rw [hexp x])
  have hgL2 : MemLp g 2 π := (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hgsq
  -- each coordinate is square integrable under the chain measure
  have hSk : ∀ k : ℕ, MemLp (fun ω : ℕ → X => g (ω (k + 1))) 2 (chainMeasure P π) := by
    intro k
    have hmap : Measure.map (fun ω : ℕ → X => ω (k + 1)) (chainMeasure P π) = π :=
      MarkovChainCLT.map_coord_chainMeasure P π hinv (k + 1)
    have h1 : MemLp g 2 (Measure.map (fun ω : ℕ → X => ω (k + 1)) (chainMeasure P π)) := by
      rw [hmap]; exact hgL2
    have hm1 : AEStronglyMeasurable g
        (Measure.map (fun ω : ℕ → X => ω (k + 1)) (chainMeasure P π)) := by
      rw [hmap]; exact hgm.aestronglyMeasurable
    have h2 := (memLp_map_measure_iff hm1
      (measurable_pi_apply (k + 1)).aemeasurable).mp h1
    exact h2
  -- the partial sum is square integrable
  have hsum : MemLp (fun ω : ℕ → X => ∑ k ∈ Finset.range n, g (ω (k + 1))) 2
      (chainMeasure P π) := by
    have h := memLp_finset_sum' (μ := chainMeasure P π) (p := 2) (Finset.range n)
      (f := fun k (ω : ℕ → X) => g (ω (k + 1))) (fun k _ => hSk k)
    have hfun : (∑ i ∈ Finset.range n, (fun ω : ℕ → X => g (ω (i + 1))))
        = fun ω : ℕ → X => ∑ k ∈ Finset.range n, g (ω (k + 1)) := by
      ext ω
      simp
    rw [hfun] at h
    exact h
  have hsumsq : Integrable
      (fun ω : ℕ → X => (∑ k ∈ Finset.range n, g (ω (k + 1))) ^ 2) (chainMeasure P π) :=
    hsum.integrable_sq
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    simpa using (integrable_zero (ℕ → X) ℝ (chainMeasure P π))
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hkey : ∀ ω : ℕ → X, (Real.sqrt n * (sampleAvg r n ω - c)) ^ 2
        = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, g (ω (k + 1))) ^ 2 := by
      intro ω
      have hsplit : ∑ k ∈ Finset.range n, g (ω (k + 1))
          = (∑ k ∈ Finset.range n, r (ω (k + 1))) - (n : ℝ) * c := by
        rw [hg]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        simp [mul_comm]
      have havg : sampleAvg r n ω - c
          = (n : ℝ)⁻¹ * ((∑ k ∈ Finset.range n, r (ω (k + 1))) - (n : ℝ) * c) := by
        rw [MarkovChainCLT.sampleAvg]
        field_simp
      rw [havg, hsplit, mul_pow, mul_pow, Real.sq_sqrt hnR.le]
      field_simp
    have := hsumsq.const_mul ((n : ℝ)⁻¹)
    exact this.congr (by filter_upwards with ω; rw [hkey ω])
