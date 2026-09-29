-- Prove2me | solution 1 for schatten_norm_le_rank_rpow_smul_spectral_norm
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T18:56:26.625038+00:00
-- url     : https://prove2.me/submissions/efc2074b-0e35-49e1-bc87-b4772f33c24e

import Definitions.Def_matrix_completion_schatten
import Theorems.Thm_spectral_norm_eq_singular_value_zero
import Mathlib.Analysis.InnerProductSpace.SingularValues

open MatrixCompletion
open scoped BigOperators

/-- Source: Candès–Recht 2009 (arXiv:0805.4471), §6.1, the operator/Schatten
comparison stated right after Lemma 6.1 (cr.txt lines 1670-1690): for an `n×n`
matrix and `q ≥ log n`, `‖X‖_{S_q} ≤ rank(X)^{1/q} · ‖X‖`, since each singular
value `σ_k ≤ σ₀ = ‖X‖` and only `rank` of them are nonzero; with `q ≥ log rank`
the prefactor collapses to `≤ e^{1/2}` (Horn–Johnson §7.3 / §5.6). This node is the
`rank^{1/q}` half; the window-collapse `rank^{1/q} ≤ e^{1/2}` is the separate
`gram_schatten_le_exp_half_variance_scale`/Node-B machinery (`6090ab2e`). Reuses the
Proved B0 equality `spectral_norm_eq_singular_value_zero` (`spectralNorm X = σ₀`). -/
theorem solution :
    ∀ {n1 n2 : ℕ} (q : ℝ) (X : Matrix (Fin n1) (Fin n2) ℝ),
      1 ≤ q →
        schattenNorm q X ≤
          Real.rpow
            ((Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) : ℝ)) q⁻¹
            * spectralNorm X := by
  intro n1 n2 q X hq
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le one_pos hq
  set T := Matrix.toEuclideanLin X with hT
  set σ := fun k : ℕ => T.singularValues k with hσ
  set r : ℕ := Module.finrank ℝ (LinearMap.range T) with hr
  have hσnn : ∀ k, 0 ≤ σ k := fun k => T.singularValues_nonneg k
  rw [spectral_norm_eq_singular_value_zero X]
  show schattenNorm q X ≤ Real.rpow (r:ℝ) q⁻¹ * σ 0
  unfold schattenNorm
  set S := ∑ k : Fin n2, Real.rpow (σ (↑k)) q with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (hσnn _) q)
  have hrhs : 0 ≤ Real.rpow (r:ℝ) q⁻¹ * σ 0 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _) (hσnn 0)
  show S ^ q⁻¹ ≤ Real.rpow (r:ℝ) q⁻¹ * σ 0
  rw [Real.rpow_inv_le_iff_of_pos hSnn hrhs hq0]
  have hexpand : (Real.rpow (r:ℝ) q⁻¹ * σ 0) ^ q
      = (r:ℝ) * (σ 0) ^ q := by
    have h1 : (Real.rpow (r:ℝ) q⁻¹ * σ 0) ^ q
        = (Real.rpow (r:ℝ) q⁻¹) ^ q * (σ 0) ^ q :=
      Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg r) _) (hσnn 0)
    have h2 : (Real.rpow (r:ℝ) q⁻¹) ^ q = (r:ℝ) := by
      rw [show ((r:ℝ).rpow q⁻¹) ^ q = (r:ℝ).rpow (q⁻¹ * q) from
            (Real.rpow_mul (Nat.cast_nonneg r) q⁻¹ q).symm,
        inv_mul_cancel₀ (ne_of_gt hq0)]
      exact Real.rpow_one _
    rw [h1, h2]
  rw [hexpand]
  rw [hS]
  set P : Finset (Fin n2) := Finset.univ.filter (fun k : Fin n2 => (↑k : ℕ) < r) with hP
  have hsplit : (∑ k : Fin n2, Real.rpow (σ (↑k)) q)
      = ∑ k ∈ P, Real.rpow (σ (↑k)) q := by
    rw [hP, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : (↑k : ℕ) < r
    · simp [hk]
    · have hz : σ (↑k) = 0 := by
        rw [hσ]
        exact (T.singularValues_eq_zero_iff_le_finrank_range).mpr (not_lt.mp hk)
      simp [hk, hz, Real.zero_rpow (ne_of_gt hq0)]
  rw [hsplit]
  have hbound : ∀ k ∈ P, Real.rpow (σ (↑k)) q ≤ Real.rpow (σ 0) q := by
    intro k _
    apply Real.rpow_le_rpow (hσnn _) _ (le_of_lt hq0)
    rw [hσ]
    exact T.singularValues_antitone (Nat.zero_le _)
  calc ∑ k ∈ P, Real.rpow (σ (↑k)) q
      ≤ ∑ _k ∈ P, Real.rpow (σ 0) q := Finset.sum_le_sum hbound
    _ = (P.card : ℝ) * Real.rpow (σ 0) q := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * Real.rpow (σ 0) q := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hσnn 0) q)
          have hcardP : P.card ≤ r := by
            calc P.card
                = (P.image (fun k : Fin n2 => (↑k:ℕ))).card :=
                  (Finset.card_image_of_injective P Fin.val_injective).symm
              _ ≤ (Finset.range r).card := by
                  apply Finset.card_le_card
                  intro x hx
                  simp only [Finset.mem_image, hP, Finset.mem_filter] at hx
                  obtain ⟨k, ⟨_, hkr⟩, rfl⟩ := hx
                  exact Finset.mem_range.mpr hkr
              _ = r := Finset.card_range r
          exact_mod_cast hcardP
