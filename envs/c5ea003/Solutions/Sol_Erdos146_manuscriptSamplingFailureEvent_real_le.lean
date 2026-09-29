-- Prove2me | solution 1 for Erdos146.manuscriptSamplingFailureEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:46:24.852012+00:00
-- url     : https://prove2.me/submissions/a34dbd21-c323-4830-97ea-4d7e7e8c1303

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_Erdos146_badPairLayersRetentionEvent_real_le
import Theorems.Thm_Erdos146_hammingExpectedRetainedVertexCount_eq
import Theorems.Thm_Erdos146_hammingRetainedEdgeCount_lower_tail_probability_le
import Theorems.Thm_Erdos146_hammingRetainedVertexCount_integral_eq
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability
import Theorems.Thm_Erdos146_hammingRetentionMeasure_memLp_two
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_pair
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_vertex
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_deviation_le
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_event_eq_sum

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem hammingExpectedRetainedVertexCount_pos
    (dimension : ℕ) :
    0 < hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

theorem hammingRetentionMeasure_real_vertexPair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, hammingRetentionMeasure_real_contains_vertex]
    simp
  · rw [hammingRetentionMeasure_real_contains_pair
      dimension first second hequal]
    simp [hequal]

theorem hammingExpectedRetainedVertexSquare_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        hammingRetentionProbability dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (hammingRetentionProbability dimension -
          hammingRetentionProbability dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2) =
        hammingRetentionProbability dimension ^ 2 +
          (if first = second then
            hammingRetentionProbability dimension -
              hammingRetentionProbability dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold hammingExpectedRetainedVertexSquare
  simp_rw [hammingRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring

theorem hammingExpectedRetainedVertexVariance_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension *
        (1 - hammingRetentionProbability dimension) := by
  rw [hammingExpectedRetainedVertexSquare_eq,
    hammingExpectedRetainedVertexCount_eq]
  push_cast
  ring

theorem hammingExpectedRetainedVertexVariance_le_mean
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexVariance_eq,
    hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  have hupper := hammingRetentionProbability_le_one dimension
  have hfactor :
      0 ≤ (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension := by
    positivity
  have hle : 1 - hammingRetentionProbability dimension ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hle hfactor
  push_cast at hscaled ⊢
  nlinarith

open Classical in
theorem hammingRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold hammingRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]

theorem hammingRetainedVertexCount_sq_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension := by
  classical
  simp_rw [hammingRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold hammingExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]

theorem hammingRetainedVertexCount_variance_eq
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedVertexCount dimension))]
  change
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedVertexCount dimension retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2
  rw [hammingRetainedVertexCount_sq_integral_eq,
    hammingRetainedVertexCount_integral_eq]

theorem hammingRetainedVertexCount_variance_le
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingRetainedVertexCount_variance_eq]
  exact hammingExpectedRetainedVertexVariance_le_mean dimension

theorem hammingRetainedVertexCount_deviation_probability_le
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      hammingExpectedRetainedVertexCount dimension / threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedVertexCount dimension)
    threshold hthreshold
  rw [hammingRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      ProbabilityTheory.variance
          (hammingRetainedVertexCount dimension)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedVertexCount_variance_le dimension

theorem hammingRetainedVertexCount_upper_tail_probability_le
    (dimension : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      4 / hammingExpectedRetainedVertexCount dimension := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedVertexCount_pos dimension
  have hthreshold :
      0 < hammingExpectedRetainedVertexCount dimension / 2 := by
    positivity
  have hchebyshev := hammingRetainedVertexCount_deviation_probability_le
    dimension (hammingExpectedRetainedVertexCount dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedVertexCount dimension / 2 ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} := by
    intro retained hretained
    change
      hammingExpectedRetainedVertexCount dimension / 2 ≤
        |hammingRetainedVertexCount dimension retained -
          hammingExpectedRetainedVertexCount dimension|
    have habsolute := le_abs_self
      (hammingRetainedVertexCount dimension retained -
        hammingExpectedRetainedVertexCount dimension)
    rw [hammingExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          hammingExpectedRetainedVertexCount dimension / 2 ≤
            |hammingRetainedVertexCount dimension retained -
              hammingExpectedRetainedVertexCount dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        (hammingExpectedRetainedVertexCount dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedVertexCount dimension := by
      field_simp [hmean.ne']
      ring

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
      (manuscriptSamplingFailureEvent layerSizes dimension) ≤
        manuscriptSamplingFailureBound depth dimension := by
  let vertexFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}
  let edgeFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}
  change
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
        manuscriptSamplingFailureBound depth dimension
  calc
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
      ((hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) +
       (hammingRetentionMeasure dimension).real vertexFailure) +
        (hammingRetentionMeasure dimension).real edgeFailure := by
      calc
        (hammingRetentionMeasure dimension).real
          ((badPairLayersRetentionEvent layerSizes dimension ∪
            vertexFailure) ∪ edgeFailure) ≤
          (hammingRetentionMeasure dimension).real
            (badPairLayersRetentionEvent layerSizes dimension ∪
              vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure :=
              MeasureTheory.measureReal_union_le _ _
        _ ≤ ((hammingRetentionMeasure dimension).real
              (badPairLayersRetentionEvent layerSizes dimension) +
            (hammingRetentionMeasure dimension).real vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure := by
              gcongr
              exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / hammingExpectedRetainedVertexCount dimension) +
        (4 / hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) +
          8 / (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ))) := by
      gcongr
      · exact badPairLayersRetentionEvent_real_le
          layerSizes hdimension hparents hbase
      · exact hammingRetainedVertexCount_upper_tail_probability_le dimension
      · exact hammingRetainedEdgeCount_lower_tail_probability_le
          dimension (manuscriptHammingRadius dimension)
    _ = manuscriptSamplingFailureBound depth dimension := by
      rfl
