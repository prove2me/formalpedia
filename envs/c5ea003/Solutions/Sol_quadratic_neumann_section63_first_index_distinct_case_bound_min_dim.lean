-- Prove2me | solution 1 for quadratic_neumann_section63_first_index_distinct_case_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:42:20.392487+00:00
-- url     : https://prove2.me/submissions/ddaa676d-729f-408d-87d3-491788f118c9

import Theorems.Thm_quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim
import Theorems.Thm_quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim
import Theorems.Thm_quadratic_neumann_first_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
import Theorems.Thm_bernoulli_finite_index_intersection_probability_from_pointwise_bounds
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32 and the p. 34 summary
display.  The full `ω₁ ≠ ω₂ = ω₃` (first-index-distinct) case at the **corrected
rectangular** five-term §6.3 summary scale `Φ + t₅`.

The paper splits the first-index-distinct contribution using
`ξ_{ω₂}² = (1 - 2p)ξ_{ω₂} + p(1-p)` into a centered part (`S₁`, Lemma 6.7) and a
mean part (`S₂`, Lemma 6.8).  This file assembles the case wrapper from the two
corrected `_min_dim` per-part leaves at the common corrected scale `Φ + t₅`:

* centered leaf (`..._first_index_distinct_centered_case_bound_min_dim`),
  giving `spectralNorm(Centered) ≤ Ccent · (Φ + t₅)`;
* mean leaf (`..._first_index_distinct_mean_case_bound_min_dim`, routed through the
  honest Lemma-6.8 `r/min` coefficient), giving `spectralNorm(Mean) ≤ Cmean · (Φ + t₅)`.

Intersecting the two events and applying the deterministic split identity closes
the case at scale `(Ccent + Cmean) · (Φ + t₅)`.
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
                (quadraticNeumannFirstIndexDistinctContribution Omega S
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
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases
      quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim with
    ⟨Ccent, ccent, hCcent, hccent, hCentered⟩
  rcases
      quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim with
    ⟨Cmean, cmean, hCmean, hcmean, hMean⟩
  refine ⟨Ccent + Cmean, 2 * max ccent cmean, by positivity, by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set Φ : ℝ :=
    ((μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 +
      μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
      Real.sqrt (β * logN) *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) +
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) +
      Real.sqrt (β * logN) * μ₀ ^ 2 *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
            Real.sqrt ((N * R) / (↑(min n₁ n₂)))) with hΦ
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hCcent_le : Ccent ≤ C' := le_trans (by linarith [hCmean]) hC'
  have hCmean_le : Cmean ≤ C' := le_trans (by linarith [hCcent]) hC'
  have hccmax : ccent ≤ max ccent cmean := le_max_left _ _
  have hcmmax : cmean ≤ max ccent cmean := le_max_right _ _
  have hpr := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  obtain ⟨hp0, hp1⟩ := hpr
  have hfail_nonneg : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) :=
    Real.rpow_nonneg (by positivity) _
  have hCent :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
              Ccent * Φ) ≥
        1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := hCentered C' hCcent_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using this
  have hMn :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
              Cmean * Φ) ≥
        1 - cmean * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := hMean C' hCmean_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using this
  have hCent' :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
              Ccent * Φ) ≥
        1 - (max ccent cmean) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    le_trans (by
      have := mul_le_mul_of_nonneg_right hccmax hfail_nonneg
      linarith) hCent
  have hMn' :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
              Cmean * Φ) ≥
        1 - (max ccent cmean) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    le_trans (by
      have := mul_le_mul_of_nonneg_right hcmmax hfail_nonneg
      linarith) hMn
  let Event : Bool → Finset (Fin n₁ × Fin n₂) → Prop :=
    fun b Omega =>
      match b with
      | false =>
          spectralNorm
            (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
            Ccent * Φ
      | true =>
          spectralNorm
            (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
            Cmean * Φ
  have hPoint :
      ∀ b : Bool,
        bernoulliEventProb p (Event b) ≥
          1 - (max ccent cmean) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro b
    cases b with
    | false => exact hCent'
    | true => exact hMn'
  have hInter :=
    bernoulli_finite_index_intersection_probability_from_pointwise_bounds
      (ι := Bool) p (max ccent cmean) (Real.rpow (↑(max n₁ n₂)) (-β)) Event
      hp0 hp1 hPoint
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  rw [hcard] at hInter
  have hCombine :
      ∀ Omega,
        (∀ b : Bool, Event b Omega) →
        spectralNorm
            (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
          (Ccent + Cmean) * Φ := by
    intro Omega hΩ
    exact
      quadratic_neumann_first_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
        S Omega p Ccent Cmean Φ (hΩ false) (hΩ true)
  have hMono :=
    bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
      (fun Omega => ∀ b : Bool, Event b Omega)
      (fun Omega =>
        spectralNorm
          (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
          (Ccent + Cmean) * Φ)
      hp0 hp1 hCombine
  have hFinal :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
              (Ccent + Cmean) * Φ) ≥
        1 - (2 * max ccent cmean) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    refine le_trans ?_ hMono
    calc
      1 - 2 * max ccent cmean * Real.rpow (↑(max n₁ n₂)) (-β)
          = 1 - 2 * (max ccent cmean) * Real.rpow (↑(max n₁ n₂)) (-β) := by ring
      _ ≤ _ := hInter
  simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using hFinal
