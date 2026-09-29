-- Prove2me | solution 1 for response_centered_sampling_quadratic_coefficient_rate_bound_from_sign_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T15:33:19.318994+00:00
-- url     : https://prove2.me/submissions/070a5a19-5783-470c-9b43-8eca2ab5fc04

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Order
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma entrySupNorm_le_spectralNorm {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm X ≤ spectralNorm X := by
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  let e : EuclideanSpace ℝ (Fin n₂) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)
  calc
    |X i j| = ‖T e i‖ := by
      simp [T, e, Real.norm_eq_abs]
    _ ≤ ‖T e‖ := PiLp.norm_apply_le (T e) i
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = spectralNorm X := by
      simp [T, e, spectralNorm]

theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (Y : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          Rop (centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (signMatrix S)) →
        entrySupNorm Y ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm (signMatrix S) := by
  intro hCfixed hCresp
  refine ⟨Cresp * Cfixed, mul_pos hCresp hCfixed, ?_⟩
  intro β _hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ _hr _hm _hμ₀ _hμ₁
    Omega Y Rop hY hRop hCentered
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let scale : ℝ :=
    Real.sqrt
      ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p)
  have hCentered' :
      spectralNorm (centeredSamplingFluctuation Omega p (signMatrix S)) ≤
        Cfixed * scale * entrySupNorm (signMatrix S) := by
    simpa [p, scale, CenteredSamplingSpectralBound] using hCentered
  calc
    entrySupNorm Y ≤ spectralNorm Y :=
      entrySupNorm_le_spectralNorm hn₁ hn₂ Y
    _ = spectralNorm
        (Rop (centeredSamplingFluctuation Omega p (signMatrix S))) := by
          rw [hY]
    _ ≤ Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
        spectralNorm (centeredSamplingFluctuation Omega p (signMatrix S)) :=
          hRop (centeredSamplingFluctuation Omega p (signMatrix S))
    _ ≤ Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
        (Cfixed * scale * entrySupNorm (signMatrix S)) := by
          exact mul_le_mul_of_nonneg_left hCentered'
            (mul_nonneg
              (mul_nonneg (le_of_lt hCresp) (by positivity))
              (by positivity))
    _ = (Cresp * Cfixed) * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
          scale * entrySupNorm (signMatrix S) := by
          ring
