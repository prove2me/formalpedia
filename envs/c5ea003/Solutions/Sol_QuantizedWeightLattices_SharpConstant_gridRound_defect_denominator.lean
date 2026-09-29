-- Prove2me | solution 1 for QuantizedWeightLattices.SharpConstant.gridRound_defect_denominator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:59:46.339779+00:00
-- url     : https://prove2.me/submissions/21a4e635-bafe-4bbf-83a6-5cc95ea3cba3

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q) (hk : k ≤ q) (x y : ℝ) :
    f (gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y))
      ≤ (k / q : ℝ) * f (gridRound δ x) + (1 - (k / q : ℝ)) * f (gridRound δ y)
        + (L : ℝ) * (δ * (1 - 1 / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (k : ℝ) ≤ q := by exact_mod_cast hk
  have hl0 : (0 : ℝ) ≤ k / q := div_nonneg (Nat.cast_nonneg k) hqR.le
  have hl1 : (k / q : ℝ) ≤ 1 := (div_le_one hqR).2 hkR
  -- rounding the combination lands within `δ (1 - 1/q)` of the combination of rounded points
  have key : |gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y)
      - ((k / q : ℝ) * gridRound δ x + (1 - (k / q : ℝ)) * gridRound δ y)| ≤ δ * (1 - 1 / q) := by
    unfold gridRound
    obtain ⟨X, hX⟩ : ∃ X : ℤ, X = round (x / δ) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = round (y / δ) := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℤ, R = round (((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y) / δ) :=
      ⟨_, rfl⟩
    rw [← hX, ← hY, ← hR]
    have bnd : ∀ (z : ℝ) (Z : ℤ), Z = round z → (Z : ℝ) ≤ z + 1 / 2 ∧ z - 1 / 2 < Z := by
      intro z Z hZ
      rw [hZ, round_eq]
      exact ⟨by linarith [Int.floor_le (z + 1 / 2)], by linarith [Int.lt_floor_add_one (z + 1 / 2)]⟩
    obtain ⟨hX1, hX2⟩ := bnd _ X hX
    obtain ⟨hY1, hY2⟩ := bnd _ Y hY
    obtain ⟨hR1, hR2⟩ := bnd _ R hR
    have hw : ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y) / δ
        = (k / q : ℝ) * (x / δ) + (1 - (k / q : ℝ)) * (y / δ) := by
      field_simp
    rw [hw] at hR1 hR2
    -- the convex combination of the rounded coordinates lies in `(w - 1/2, w + 1/2]`
    have hc1 : (k / q : ℝ) * X + (1 - (k / q : ℝ)) * Y
        ≤ (k / q : ℝ) * (x / δ) + (1 - (k / q : ℝ)) * (y / δ) + 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hX1 hl0, mul_le_mul_of_nonneg_left hY1 (sub_nonneg.2 hl1)]
    have hc2 : (k / q : ℝ) * (x / δ) + (1 - (k / q : ℝ)) * (y / δ) - 1 / 2
        < (k / q : ℝ) * X + (1 - (k / q : ℝ)) * Y := by
      rcases hl0.eq_or_lt with h0 | h0
      · rw [← h0]
        linarith
      · nlinarith [mul_lt_mul_of_pos_left hX2 h0, mul_le_mul_of_nonneg_left hY2.le (sub_nonneg.2 hl1)]
    -- the integer `q R - k X - (q - k) Y` lies strictly between `-q` and `q`
    have hn : ((q * R - k * X - (q - k) * Y : ℤ) : ℝ)
        = q * ((R : ℝ) - ((k / q : ℝ) * X + (1 - (k / q : ℝ)) * Y)) := by
      push_cast
      field_simp
      ring
    have hlt : ((q * R - k * X - (q - k) * Y : ℤ) : ℝ) < q := by
      rw [hn]
      nlinarith
    have hgt : -(q : ℝ) < ((q * R - k * X - (q - k) * Y : ℤ) : ℝ) := by
      rw [hn]
      nlinarith
    have hlt' : q * R - k * X - (q - k) * Y < (q : ℤ) := by exact_mod_cast hlt
    have hgt' : -(q : ℤ) < q * R - k * X - (q - k) * Y := by exact_mod_cast hgt
    have habs : |((q * R - k * X - (q - k) * Y : ℤ) : ℝ)| ≤ (q : ℝ) - 1 := by
      rw [abs_le]
      constructor
      · have : -((q : ℤ) - 1) ≤ q * R - k * X - (q - k) * Y := by omega
        have := (Int.cast_le (R := ℝ)).2 this
        push_cast at this ⊢
        linarith
      · have : q * R - k * X - (q - k) * Y ≤ (q : ℤ) - 1 := by omega
        have := (Int.cast_le (R := ℝ)).2 this
        push_cast at this ⊢
        linarith
    have e : δ * (R : ℝ) - ((k / q : ℝ) * (δ * (X : ℝ)) + (1 - (k / q : ℝ)) * (δ * (Y : ℝ)))
        = δ / q * ((q * R - k * X - (q - k) * Y : ℤ) : ℝ) := by
      rw [hn]
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < δ / q)]
    calc δ / q * |((q * R - k * X - (q - k) * Y : ℤ) : ℝ)| ≤ δ / q * ((q : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = δ * (1 - 1 / q) := by field_simp
  have hlip : ∀ a b : ℝ, f a ≤ f b + (L : ℝ) * |a - b| := by
    intro a b
    have := hL.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at this
    linarith [le_abs_self (f a - f b)]
  have hconv := hf.2 (mem_univ (gridRound δ x)) (mem_univ (gridRound δ y)) hl0
    (sub_nonneg.2 hl1) (by ring)
  simp only [smul_eq_mul] at hconv
  have h1 := hlip (gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y))
    ((k / q : ℝ) * gridRound δ x + (1 - (k / q : ℝ)) * gridRound δ y)
  have h2 := mul_le_mul_of_nonneg_left key L.coe_nonneg
  linarith
