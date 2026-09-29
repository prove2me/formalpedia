-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:42:36.388889+00:00
-- url     : https://prove2.me/submissions/fcaaf54e-c686-4001-9667-be0f895c7796

import Definitions.Def_linear_neumann_offdiag_bernstein
import Mathlib.Data.Fintype.Order
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

open MatrixCompletion

/-!
Source: Candès--Recht 2008, Section 6.2, Lemma 6.6, equations
(6.15)--(6.17), and the union bound immediately after (6.17).
-/

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ w : Fin n₁ × Fin n₂, |X w.1 w.2| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h (i, j)

theorem solution
    (Cpoint cpoint Centry Cfro : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ctwo ctwo : ℝ, 0 < Ctwo ∧ 0 < ctwo ∧
      ∀ C' : ℝ,
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
                  Cpoint *
                    (Real.sqrt
                        (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Cfro * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                        (Centry * μ₁ *
                          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ctwo *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cfro * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Centry * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) ≥
          1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  rcases bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cpoint cpoint hCpoint hcpoint with
    ⟨Ctwo, ctwo, hCtwo, hctwo, hUniform⟩
  refine ⟨Ctwo, ctwo, hCtwo, hctwo, ?_⟩
  intro C' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let twoTermScale : ℝ :=
    Real.sqrt
        (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
      (Cfro * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
      (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
        (Centry * μ₁ *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
  have hPointwise' :
      ∀ w : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega2 =>
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Cpoint * twoTermScale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w
    simpa [p, twoTermScale, mul_assoc] using hPointwise w
  have hUniformEvent :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Ctwo * twoTermScale) ≥
        1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) :=
    hUniform β p twoTermScale hβ hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
      (fun w Omega2 =>
        linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2)
      hPointwise'
  have hMono :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Ctwo * twoTermScale) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            LinearNeumannOffDiagonalCoefficientBound Omega2 S p
              (Ctwo * twoTermScale)) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hAll
    exact entrySupNorm_le_of_forall_abs_le hn₁ hn₂
      (linearNeumannOffDiagonalCoefficientMatrix Omega2 S p)
      (Ctwo * twoTermScale) hAll
  simpa [p, twoTermScale, mul_assoc] using le_trans hUniformEvent hMono

