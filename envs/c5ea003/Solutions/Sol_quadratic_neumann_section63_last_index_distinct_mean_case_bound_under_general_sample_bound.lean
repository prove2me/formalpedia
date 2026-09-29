-- Prove2me | solution 1 for quadratic_neumann_section63_last_index_distinct_mean_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T10:29:38.053751+00:00
-- url     : https://prove2.me/submissions/002f76a5-3d7f-44ee-80d0-56006629aa86

import Theorems.Thm_quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF p. 33 and the p. 34 summary
display.  The mean part `S₂` of the `ω₁ = ω₂ ≠ ω₃` case after expanding
`ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`.  The paper writes the mean part as
`p^{-1}[P_T(P_Ω - pI)(E) - (P_Ω - pI)(G)]` and controls it by Theorem 6.3
applied to the two fixed-matrix centered sampling fluctuations, giving the
four-term §6.3 summary-scale (Lemma 6.8) estimate `Φ`.

Top-level assembly of the leaf
`quadratic_neumann_section63_last_index_distinct_mean_case_bound_under_general_sample_bound`:

* the deterministic representation identity (brick 1,
  `quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response`) writes the
  mean contribution as the off-diagonal tangent-diagonal response operator applied
  to the centered sampling fluctuation of the rescaled sign matrix;
* the genuine §6.3 analytic content is the fixed-matrix response-sampling estimate
  at the summary scale `Φ` (brick 2,
  `quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound`),
  which is the Theorem 6.3 (`021320e3`) application to the rescaled sign matrix in
  the TIGHT per-entry `‖·‖∞` scale.

This is the sound general-sample route: it stays in the
`μ₁√(r/(n₁n₂))`-normalized per-entry scale and does NOT route through the
deprecated `lam`/`μ₀^{4/3}` response-operator threshold chain
(`..._mean_from_response_sampling_bound`, `..._response_operator_bound`), which
drops the `1/√(n₁n₂)` normalization.
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
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctMeanContribution Omega S
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
  -- brick 2: genuine §6.3 analytic content, the response-sampling bound at scale Φ
  rcases
      quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound with
    ⟨Cresp, cresp, hCresp, hcresp, hRespBound⟩
  refine ⟨Cresp, cresp, hCresp, hcresp, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  -- sample ratio in [0,1]
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- the response-sampling event at scale Cresp * Φ
  have hResp :=
    hRespBound C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  -- deterministic identity: mean contribution = (1-p) • off-diagonal response of the
  -- centered sampling fluctuation of the rescaled sign matrix.  Rewrite the response
  -- event into the mean-contribution event and keep the same scale Cresp * Φ.
  refine le_trans hResp ?_
  refine bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
    (fun Omega =>
      spectralNorm
        ((1 - p) •
          quadraticLastIndexDistinctOffDiagonalResponse S
            (centeredSamplingFluctuation Omega p (p⁻¹ • signMatrix S))) ≤ _)
    (fun Omega =>
      spectralNorm
        (quadraticNeumannLastIndexDistinctMeanContribution Omega S p) ≤ _)
    hp0 hp1 ?_
  intro Omega hΩ
  rw [quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response Omega S p]
  exact hΩ
