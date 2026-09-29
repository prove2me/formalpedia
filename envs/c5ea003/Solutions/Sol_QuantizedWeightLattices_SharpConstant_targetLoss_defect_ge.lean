-- Prove2me | solution 1 for QuantizedWeightLattices.SharpConstant.targetLoss_defect_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:27:05.844843+00:00
-- url     : https://prove2.me/submissions/43c444ea-5df8-4ae4-9fa4-7bddebf37143

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {δ ε : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n)
    (h : ApproxConvexOn ε univ (targetLoss δ ∘ gridRound δ)) :
    δ - δ / n ≤ ε := by
  -- the explicit defect at `±δ/2` with weights `1 - 1/n`, `1/n`
  have hdef : ∀ n : ℕ, 3 ≤ n →
      targetLoss δ (gridRound δ ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))))
        - ((1 - 1 / (n : ℝ)) * targetLoss δ (gridRound δ (δ / 2))
          + (1 / (n : ℝ)) * targetLoss δ (gridRound δ (-(δ / 2))))
      = δ * (1 - 1 / (n : ℝ)) := by
    intro n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    -- the three grid roundings: `δ/2 - δ/n ↦ 0`, `δ/2 ↦ δ`, `-δ/2 ↦ 0`
    have r1 : gridRound δ ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))) = 0 := by
      unfold gridRound
      have e : ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))) / δ = 1 / 2 - 1 / n := by
        field_simp
        ring
      rw [e, round_eq]
      have : ⌊1 / 2 - 1 / (n : ℝ) + 1 / 2⌋ = 0 := by
        rw [Int.floor_eq_zero_iff]
        constructor
        · have : 1 / (n : ℝ) ≤ 1 / 3 := by
            rw [div_le_div_iff₀ hn0 (by norm_num)]
            linarith
          linarith
        · have : 0 < 1 / (n : ℝ) := by positivity
          linarith
      rw [this]
      simp
    have r2 : gridRound δ (δ / 2) = δ := by
      unfold gridRound
      have e : δ / 2 / δ = 1 / 2 := by field_simp
      rw [e, round_eq]
      norm_num
    have r3 : gridRound δ (-(δ / 2)) = 0 := by
      unfold gridRound
      have e : -(δ / 2) / δ = -(1 / 2) := by field_simp
      rw [e, round_eq]
      norm_num
    rw [r1, r2, r3]
    unfold targetLoss
    rw [sub_self, abs_zero, zero_sub, abs_neg, abs_of_pos hδ]
    ring
  -- any admissible `ε` dominates that defect
  have hge : ∀ n : ℕ, 3 ≤ n → δ * (1 - 1 / (n : ℝ)) ≤ ε := by
    intro n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have ha : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    have hb : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have hc := h (mem_univ (δ / 2)) (mem_univ (-(δ / 2))) ha hb (by ring)
    simp only [Function.comp, smul_eq_mul] at hc
    have := hdef n hn
    linarith
  have := hge n hn
  have e : δ * (1 - 1 / (n : ℝ)) = δ - δ / n := by ring
  linarith
