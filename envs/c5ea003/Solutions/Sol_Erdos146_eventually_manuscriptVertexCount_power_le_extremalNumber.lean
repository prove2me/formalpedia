-- Prove2me | solution 1 for Erdos146.eventually_manuscriptVertexCount_power_le_extremalNumber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:52:37.471205+00:00
-- url     : https://prove2.me/submissions/fd1c4fd3-aca2-4a28-812f-a387cd5dae38

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Theorems.Thm_Erdos146_eventually_expectedRetainedEdge_le_extremalNumber
import Theorems.Thm_Erdos146_eventually_manuscriptExpectedRetainedEdge_entropy_lower
import Theorems.Thm_Erdos146_exp_mul_div_nat_succ_tendsto_atTop
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_eq_exp
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_tendsto_atTop
import Theorems.Thm_Erdos146_manuscriptEntropyGap_pos
import Theorems.Thm_Erdos146_manuscriptExtremalPower_pos
import Theorems.Thm_Erdos146_midpointBeta_lt_one

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower :
    sampledHammingEdgeEntropyRate =
      (1 - midpointBeta) * manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
  have hmidpoint :
      entropyUpperEndpoint - midpointBeta =
        certifiedWindowWidth / 2 := by
    have hwindow := entropyWindow_eq_certifiedWindowWidth
    unfold midpointBeta
    linarith
  have hupper :
      binaryEntropy tau = (entropyUpperEndpoint + 1) / 2 := by
    unfold entropyUpperEndpoint
    ring
  have hgain :
      (1 - midpointBeta) * exponentGain =
        certifiedWindowWidth / 8 := by
    have hnonzero : 1 - midpointBeta ≠ 0 :=
      (sub_pos.mpr midpointBeta_lt_one).ne'
    unfold exponentGain
    field_simp [hnonzero]
  have hbits :
      1 - 2 * midpointBeta + binaryEntropy tau =
        (1 - midpointBeta) *
            ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8 := by
    nlinarith [hmidpoint, hupper, hgain]
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  calc
    sampledHammingEdgeEntropyRate =
        (1 - 2 * midpointBeta + binaryEntropy tau) *
          Real.log 2 := by
      unfold sampledHammingEdgeEntropyRate
      rw [hentropy]
      ring
    _ = ((1 - midpointBeta) *
          ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8) * Real.log 2 := by
      rw [hbits]
    _ = (1 - midpointBeta) *
          manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
      unfold manuscriptExtremalPower manuscriptEntropyGap
      ring

theorem manuscriptVertexCount_le_four_wordMean
    (dimension : ℕ)
    (hmean :
      1 ≤ hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) :
    (manuscriptVertexCount dimension : ℝ) ≤
      4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hargument :
      0 ≤ 3 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
    positivity [hammingRetentionProbability_pos dimension]
  have hceiling :
      (manuscriptVertexCount dimension : ℝ) <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold manuscriptVertexCount
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_manuscriptVertexCount_le_four_wordMean :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ≤
        4 * (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    hammingRetentionProbability_mul_wordCount_tendsto_atTop (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact manuscriptVertexCount_le_four_wordMean dimension hdimension

theorem eventually_manuscriptEntropyGap_dominates_power_constant :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      2 * (4 : ℝ) ^ manuscriptExtremalPower ≤
        Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ) := by
  exact Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop
      manuscriptEntropyGap manuscriptEntropyGap_pos)
    (2 * (4 : ℝ) ^ manuscriptExtremalPower)

theorem eventually_manuscriptVertexCount_power_le_expectedRetainedEdge :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ^
          manuscriptExtremalPower ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
  have hlower :=
    eventually_manuscriptExpectedRetainedEdge_entropy_lower
      manuscriptEntropyGap manuscriptEntropyGap_pos
  have hvertex :=
    eventually_manuscriptVertexCount_le_four_wordMean
  have hconstant :=
    eventually_manuscriptEntropyGap_dominates_power_constant
  filter_upwards [hlower, hvertex, hconstant] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hconstant_half :
      (4 : ℝ) ^ manuscriptExtremalPower ≤
        (Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower +
          manuscriptEntropyGap * (dimension : ℝ) =
        (dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - manuscriptEntropyGap) := by
    rw [sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower]
    ring
  calc
    (manuscriptVertexCount dimension : ℝ) ^
        manuscriptExtremalPower ≤
      (4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^
          manuscriptExtremalPower := by
        apply Real.rpow_le_rpow
        · positivity
        · exact hvertex_bound
        · exact manuscriptExtremalPower_pos.le
    _ = (4 : ℝ) ^ manuscriptExtremalPower *
        Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) := by
      rw [hammingRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
        ← Real.exp_mul]
    _ ≤ Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) *
        ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      calc
        (4 : ℝ) ^ manuscriptExtremalPower *
            Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) =
          Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            (4 : ℝ) ^ manuscriptExtremalPower := by ring
        _ ≤ Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
              ((dimension + 1 : ℕ) : ℝ)) / 2) :=
          mul_le_mul_of_nonneg_left hconstant_half
            (Real.exp_pos _).le
    _ = (Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
              manuscriptExtremalPower +
            manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]
      ring
    _ = (Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - manuscriptEntropyGap)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [hexponent]
    _ ≤ hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
      gcongr

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hextremal⟩ :=
    eventually_expectedRetainedEdge_le_extremalNumber
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards
    [eventually_manuscriptVertexCount_power_le_expectedRetainedEdge,
      hextremal] with dimension hpower hbound
  exact hpower.trans hbound
