-- Prove2me | solution 2 for QuantizedWeightLattices.SharpConstant.gridRound_defect_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:21:48.701933+00:00
-- url     : https://prove2.me/submissions/365c980a-71e1-4d83-984d-fb9873a6babd

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {δ ε : ℝ} (hδ : 0 < δ)
    (h : ApproxConvexOn ε univ (targetLoss δ ∘ gridRound δ)) : δ ≤ ε := by
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
  -- let `n → ∞`
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (max 3 (δ / (δ - ε)))
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast this.le
  have hnR : (0 : ℝ) < n := by
    have : (3 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    linarith
  have hbig : δ / (δ - ε) < n := lt_of_le_of_lt (le_max_right _ _) hn
  rw [div_lt_iff₀ (by linarith)] at hbig
  have := hge n hn3
  have e : δ * (1 - 1 / (n : ℝ)) = δ - δ / n := by ring
  rw [e] at this
  have : δ / n < δ - ε := by
    rw [div_lt_iff₀ hnR]
    linarith
  linarith
