-- Prove2me | solution 1 for QuantizedWeightLattices.SharpConstant.gridRound_midpoint_defect
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:50:16.630305+00:00
-- url     : https://prove2.me/submissions/90d7e0b1-e872-4c2f-9e1c-aee2251cf892

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    f (gridRound δ ((x + y) / 2))
      ≤ (1 / 2 : ℝ) * f (gridRound δ x) + (1 / 2 : ℝ) * f (gridRound δ y)
        + (L : ℝ) * (δ / 2) := by
  -- rounding the midpoint lands within `δ/2` of the midpoint of the rounded points
  have key : ∀ x y : ℝ,
      |gridRound δ ((x + y) / 2) - (gridRound δ x + gridRound δ y) / 2| ≤ δ / 2 := by
    intro x y
    unfold gridRound
    have hw : (x + y) / 2 / δ = (x / δ + y / δ) / 2 := by
      field_simp
    rw [hw]
    obtain ⟨X, hX⟩ : ∃ X : ℤ, X = round (x / δ) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = round (y / δ) := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℤ, R = round ((x / δ + y / δ) / 2) := ⟨_, rfl⟩
    rw [← hX, ← hY, ← hR]
    -- `round z - z ∈ (-1/2, 1/2]`
    have bnd : ∀ (z : ℝ) (Z : ℤ), Z = round z → (Z : ℝ) ≤ z + 1 / 2 ∧ z - 1 / 2 < Z := by
      intro z Z hZ
      rw [hZ, round_eq]
      exact ⟨by linarith [Int.floor_le (z + 1 / 2)], by linarith [Int.lt_floor_add_one (z + 1 / 2)]⟩
    obtain ⟨hX1, hX2⟩ := bnd _ X hX
    obtain ⟨hY1, hY2⟩ := bnd _ Y hY
    obtain ⟨hR1, hR2⟩ := bnd _ R hR
    -- so the integer `2R - X - Y` lies strictly between `-2` and `2`
    have hk1 : ((2 * R - X - Y : ℤ) : ℝ) < 2 := by
      push_cast
      linarith
    have hk2 : (-2 : ℝ) < ((2 * R - X - Y : ℤ) : ℝ) := by
      push_cast
      linarith
    have hk1' : 2 * R - X - Y < 2 := by exact_mod_cast hk1
    have hk2' : -2 < 2 * R - X - Y := by exact_mod_cast hk2
    have hk : |((2 * R - X - Y : ℤ) : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have : -1 ≤ 2 * R - X - Y := by omega
        exact_mod_cast this
      · have : 2 * R - X - Y ≤ 1 := by omega
        exact_mod_cast this
    have e : δ * (R : ℝ) - (δ * (X : ℝ) + δ * (Y : ℝ)) / 2
        = δ / 2 * ((2 * R - X - Y : ℤ) : ℝ) := by
      push_cast
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < δ / 2)]
    exact mul_le_of_le_one_right (by positivity) hk
  have hlip : ∀ a b : ℝ, f a ≤ f b + (L : ℝ) * |a - b| := by
    intro a b
    have := hL.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at this
    linarith [le_abs_self (f a - f b)]
  have hconv := hf.2 (mem_univ (gridRound δ x)) (mem_univ (gridRound δ y))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hconv
  have hm : (1 / 2 : ℝ) * gridRound δ x + 1 / 2 * gridRound δ y
      = (gridRound δ x + gridRound δ y) / 2 := by ring
  rw [hm] at hconv
  have h1 := hlip (gridRound δ ((x + y) / 2)) ((gridRound δ x + gridRound δ y) / 2)
  have h2 := mul_le_mul_of_nonneg_left (key x y) L.coe_nonneg
  linarith
