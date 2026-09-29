-- Prove2me | solution 2 for quadratic_neumann_section63_all_distinct_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T10:12:21.801884+00:00
-- url     : https://prove2.me/submissions/1ee209e0-4519-4032-ae58-01ef061f3524

import Theorems.Thm_quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_section63_all_distinct_from_decoupled_section63_bound
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF pp. 33--34.

This is the all-distinct case in the five-way partition (6.20).  The paper
first applies a triple decoupling argument, then estimates the fully decoupled
term via equation (6.23), two nested Lemma 6.6 coefficient estimates, and
Theorem 6.3 in the outer sample.  This sketch performs only the top-level
assembly: apply the decoupled Section 6.3 estimate and transfer it back to the
original one-copy all-distinct contribution.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 C *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases
      quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound with
    ⟨Cdec, cdec, hCdec, hcdec, hDecoupled⟩
  rcases
      quadratic_neumann_section63_all_distinct_from_decoupled_section63_bound
        Cdec cdec hCdec hcdec with
    ⟨Ctrans, ctrans, hCtrans, hctrans, hTransfer⟩
  let C : ℝ := max Cdec Ctrans
  refine ⟨C, ctrans, ?_, hctrans, ?_⟩
  · dsimp [C]
    exact lt_of_lt_of_le hCdec (le_max_left _ _)
  · intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hCdec_le : Cdec ≤ C' := le_trans (by dsimp [C]; exact le_max_left _ _) hC'
    have hCtrans_le_C : Ctrans ≤ C := by
      dsimp [C]
      exact le_max_right _ _
    have hDecoupledProb :
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cdec *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
      exact hDecoupled C' hCdec_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa [C] using
      hTransfer C hCtrans_le_C β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hDecoupledProb
