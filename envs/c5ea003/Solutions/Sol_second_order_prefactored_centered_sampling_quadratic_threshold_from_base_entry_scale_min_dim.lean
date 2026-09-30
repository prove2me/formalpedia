-- Prove2me | solution 1 for second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:08.728827+00:00
-- url     : https://prove2.me/submissions/1e912270-938b-4bb3-8e63-8c50b3ecd8ff

import Mathlib
import Definitions.Def_matrix_completion_tangent

-- Source module: RowNorm.lean
open MatrixCompletion

section RectangularSamplingSec

def rs_rowMatrix {n1 n2 : ℕ} (i : Fin n1) (a : ℝ) : RealMatrix n1 n2 :=
  fun k _ => if k = i then a else 0

theorem rs_spectralNorm_rowMatrix {n1 n2 : ℕ} (i : Fin n1) (a : ℝ) :
    MatrixCompletion.spectralNorm (rs_rowMatrix (n2 := n2) i a) = |a| * Real.sqrt n2 := by
  let x : EuclideanSpace ℝ (Fin n1) := EuclideanSpace.single i a
  let y : EuclideanSpace ℝ (Fin n2) := WithLp.toLp 2 (fun _ => 1)
  have hm : rs_rowMatrix i a = Matrix.vecMulVec x (star y) := by
    ext k j
    simp [rs_rowMatrix, x, y, Matrix.vecMulVec_apply, Pi.single_apply]
  have hl : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (rs_rowMatrix i a)) =
      InnerProductSpace.rankOne ℝ x y := by
    have heq : Matrix.toEuclideanLin (rs_rowMatrix i a) =
        (InnerProductSpace.rankOne ℝ x y).toLinearMap := by
      apply Matrix.toEuclideanLin.symm.injective
      simpa only [LinearEquiv.symm_apply_apply,
        InnerProductSpace.symm_toEuclideanLin_rankOne] using hm
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun heq z
  have hx : ‖x‖ = |a| := by simp [x, Real.norm_eq_abs]
  have hy : ‖y‖ = Real.sqrt n2 := by
    simp [EuclideanSpace.norm_eq, y]
  unfold MatrixCompletion.spectralNorm
  rw [hl, InnerProductSpace.norm_rankOne, hx, hy]

theorem rs_entrySupNorm_rowMatrix {n1 n2 : ℕ} (i : Fin n1) (a : ℝ) (hn2 : 0 < n2) :
    entrySupNorm (rs_rowMatrix (n2 := n2) i a) = |a| := by
  have : Nonempty (Fin n1) := ⟨i⟩
  have : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
  unfold entrySupNorm
  apply le_antisymm
  · apply ciSup_le
    intro k
    apply ciSup_le
    intro j
    by_cases h : k = i <;> simp [rs_rowMatrix, h, abs_nonneg]
  · apply le_ciSup_of_le (Set.finite_range _).bddAbove i
    apply le_ciSup_of_le (Set.finite_range _).bddAbove (⟨0, hn2⟩ : Fin n2)
    simp [rs_rowMatrix]

end RectangularSamplingSec

-- Source module: Arithmetic.lean
section RectangularSamplingSec

theorem rs_inverse_cube_mul_sqrt_pow_eight (q : ℝ) (hq : 0 < q) :
    q⁻¹ ^ 3 * Real.sqrt (q ^ 8) = q := by
  rw [show q ^ 8 = (q ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  field_simp

theorem rs_spectral_scale_bound (q : ℝ) (hq : 0 < q)
    (hlog : 1 ≤ 6 * Real.log (q ^ 8)) :
    q ≤ Real.sqrt ((3 * q ^ 8 * Real.log (q ^ 8)) / (1 / 2)) * q⁻¹ ^ 3 := by
  have hsq : (q ^ 4) ^ 2 ≤ (3 * q ^ 8 * Real.log (q ^ 8)) / (1 / 2) := by
    calc
      (q ^ 4) ^ 2 = q ^ 8 := by ring
      _ ≤ q ^ 8 * (6 * Real.log (q ^ 8)) := le_mul_of_one_le_right (by positivity) hlog
      _ = _ := by ring
  have h := mul_le_mul_of_nonneg_right (Real.le_sqrt_of_sq_le hsq)
    (show 0 ≤ q⁻¹ ^ 3 by positivity)
  have heq : q ^ 4 * q⁻¹ ^ 3 = q := by
    field_simp
  simpa only [heq] using h

theorem rs_exists_dimensions (C : ℝ) :
    ∃ q m : ℕ, 0 < q ∧ q ≤ q ^ 8 ∧ m ≤ q * q ^ 8 ∧
      (m : ℝ) / ((q : ℝ) * (q : ℝ) ^ 8) = 1 / 2 ∧
      C < (q : ℝ) ∧
      (q : ℝ) ^ 8 * (3 * Real.log ((q : ℝ) ^ 8)) ≤ (m : ℝ) ∧
      1 ≤ 6 * Real.log ((q : ℝ) ^ 8) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max C 48)
  have hkC : C < (k : ℝ) := (le_max_left C 48).trans_lt hk
  have hk48 : (48 : ℝ) ≤ k := (le_max_right C 48).trans hk.le
  have hk0 : (0 : ℝ) < k := by linarith
  have hkNat : 48 ≤ k := by exact_mod_cast hk48
  let q : ℕ := 4 * k ^ 2
  let m : ℕ := 2 * k ^ 2 * q ^ 8
  have hq : (q : ℝ) = 4 * (k : ℝ) ^ 2 := by simp [q]
  have hqsq : (q : ℝ) = (2 * (k : ℝ)) ^ 2 := by rw [hq]; ring
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := hqpos
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq0 : (q : ℝ) ≠ 0 := hqreal.ne'
  have hm : (m : ℝ) = 2 * (k : ℝ) ^ 2 * (q : ℝ) ^ 8 := by simp [m]
  refine ⟨q, m, hqpos, le_self_pow₀ hq1 (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · have hcoef : 2 * k ^ 2 ≤ q := by dsimp [q]; omega
    exact Nat.mul_le_mul_right (q ^ 8) hcoef
  · rw [hm]
    apply (div_eq_iff (mul_ne_zero hq0 (pow_ne_zero 8 hq0))).mpr
    rw [hq]
    ring
  · rw [hq]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  · have hlog : Real.log (q : ℝ) ≤ 4 * (k : ℝ) := by
      rw [hqsq, Real.log_pow]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * k by positivity)
      norm_num at *
      linarith
    have hbase : 24 * Real.log (q : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
      nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hk48)]
    rw [Real.log_pow, hm]
    norm_num
    calc
      (q : ℝ) ^ 8 * (3 * (8 * Real.log (q : ℝ))) =
          (q : ℝ) ^ 8 * (24 * Real.log (q : ℝ)) := by ring
      _ ≤ (q : ℝ) ^ 8 * (2 * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by ring
  · have hq2 : (2 : ℝ) ≤ q := by rw [hq]; nlinarith
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h
      exact h
    have hlogq := hlog2.trans (Real.log_le_log (by norm_num) hq2)
    rw [Real.log_pow]
    norm_num
    linarith

end RectangularSamplingSec

-- Source module: Main.lean
open MatrixCompletion

theorem solution :
    ¬ (∀ (Cfixed Cbase : ℝ),
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2))) := by
  intro h
  obtain ⟨C, _hC, hbound⟩ := h 1 1 (by norm_num) (by norm_num)
  obtain ⟨q, m, hq, hdim, hm, hp, hqC, hsample, hlog⟩ := rs_exists_dimensions C
  have hn2 : 0 < q ^ 8 := pow_pos hq 8
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  let i : Fin q := ⟨0, hq⟩
  let a : ℝ := (q : ℝ)⁻¹ ^ 3
  let B : RealMatrix q (q ^ 8) := rs_rowMatrix i a
  let Y : RealMatrix q (q ^ 8) := rs_rowMatrix i (-a)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hp' : (m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ)) = 1 / 2 := by
    simpa only [Nat.cast_pow] using hp
  have hentry : entrySupNorm B = a := by
    rw [show B = rs_rowMatrix i a from rfl, rs_entrySupNorm_rowMatrix i a hn2,
      abs_of_nonneg ha]
  have hnorm : spectralNorm Y = (q : ℝ) := by
    rw [show Y = rs_rowMatrix i (-a) from rfl, rs_spectralNorm_rowMatrix,
      abs_neg, abs_of_nonneg ha, Nat.cast_pow]
    exact rs_inverse_cube_mul_sqrt_pow_eight (q : ℝ) hqreal
  have hfluct : centeredSamplingFluctuation ∅ (1 / 2) B = Y := by
    ext k j
    by_cases hki : k = i <;>
      norm_num [centeredSamplingFluctuation, samplingProjection, B, Y, rs_rowMatrix, hki]
    ring
  have hY : Y =
      ((((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ)))⁻¹) ^ 2 *
        (1 - 3 * ((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ))) +
          3 * ((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ))) ^ 2)) •
        centeredSamplingFluctuation ∅ ((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ))) B := by
    rw [hp', hfluct]
    norm_num
  have hentryBound : entrySupNorm B ≤
      (1 : ℝ) * 1 ^ 3 * ((1 : ℝ) / (min q (q ^ 8))) ^ 3 := by
    rw [hentry, min_eq_left hdim]
    simp [a, one_div]
  have hspectral : CenteredSamplingSpectralBound ∅
      ((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ))) B
      ((1 : ℝ) * Real.sqrt ((3 * (max q (q ^ 8) : ℕ) *
        Real.log (max q (q ^ 8) : ℕ)) /
          ((m : ℝ) / ((q : ℝ) * (q ^ 8 : ℕ)))) * entrySupNorm B) := by
    unfold CenteredSamplingSpectralBound
    rw [hp', hfluct, hnorm, hentry, max_eq_right hdim]
    simpa only [one_mul, Nat.cast_pow] using rs_spectral_scale_bound (q : ℝ) hqreal hlog
  have hsample' : (m : ℝ) ≥
      (1 : ℝ) * Real.rpow 1 ((4 : ℝ) / 3) *
        (max q (q ^ 8) : ℕ) * Real.rpow (1 : ℝ) ((4 : ℝ) / 3) *
          (3 * Real.log (max q (q ^ 8) : ℕ)) := by
    simpa [max_eq_right hdim] using hsample
  have hbad := hbound 3 1 (by norm_num) (by norm_num) q (q ^ 8) 1 m 1
    hq hn2 (by norm_num) hm (by norm_num)
    (by simpa only [Nat.cast_one] using hsample') ∅ B Y hY
    (by simpa only [Nat.cast_one] using hentryBound) hspectral
  rw [hnorm] at hbad
  norm_num at hbad
  exact (not_le_of_gt hqC) hbad

#check @solution
#print axioms solution
