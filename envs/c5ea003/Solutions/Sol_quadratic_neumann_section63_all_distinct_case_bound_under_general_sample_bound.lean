-- Prove2me | solution 1 for quadratic_neumann_section63_all_distinct_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T05:28:28.391926+00:00
-- url     : https://prove2.me/submissions/8ac6c690-da84-437e-8e76-9b1c7b2d8fa1

import Theorems.Thm_quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_all_distinct_triple_decoupling_tail_bound
import Theorems.Thm_quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF p. 34 (eq. 6.23 and the summary
display).  This is the all-distinct index case `ω₁ ≠ ω₂ ≠ ω₃` of the five-way
partition (6.20) of the second quadratic Neumann correction.

Top-level assembly of `ab8f4ec6`
(`quadratic_neumann_section63_all_distinct_case_bound_under_general_sample_bound`):

* the genuine §6.3 analytic content is the fully *decoupled* three-copy estimate
  at the summary scale Φ (child A,
  `quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound`);
* it is transferred back to the original one-copy contribution using the two
  Proved generic transfers
  `quadratic_neumann_all_distinct_triple_decoupling_tail_bound` (triple → diagonal
  coupling, generic threshold/failure scale) and
  `quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail`
  (diagonal coupling → original, generic bound), exactly as in the Proved
  `quadratic_neumann_all_distinct_from_decoupled_bound` glue but with the §6.3
  summary scale Φ in place of `lam^{-3/2}`.
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
  -- genuine §6.3 analytic content: the fully decoupled three-copy bound at scale Φ
  rcases
      quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound with
    ⟨Cdec, cdec, hCdec, hcdec, hDecoupled⟩
  -- generic transfers (Proved on platform)
  rcases quadratic_neumann_all_distinct_triple_decoupling_tail_bound with
    ⟨K, L, hK, hL, hTriple⟩
  refine ⟨max Cdec (K * Cdec), L * cdec, ?_, by positivity, ?_⟩
  · exact lt_of_lt_of_le hCdec (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  -- abbreviate the summary scale Φ (the four-term factor)
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
      Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)) with hΦ
  -- Child A's hypothesis requires Cdec ≤ C'; supply it (Cdec ≤ max Cdec _ ≤ C').
  have hCdec_le : Cdec ≤ C' := le_trans (le_max_left _ _) hC'
  have hKCdec_le : K * Cdec ≤ C' := le_trans (le_max_right _ _) hC'
  have hΦnonneg : 0 ≤ Φ := by
    have hNnat : 0 < max n₁ n₂ := Nat.lt_of_lt_of_le hn₁ (le_max_left _ _)
    have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast hNnat
    have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hNnat
    have hRnn : (0 : ℝ) ≤ R := by rw [hR]; positivity
    have hMobsnn : (0 : ℝ) ≤ Mobs := by rw [hMobs]; positivity
    have hlogNnn : 0 ≤ logN := by
      rw [hlogN]; exact Real.log_nonneg hN1
    have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
    have hμ₁nn : (0 : ℝ) ≤ μ₁ := le_trans zero_le_one hμ₁
    have hβnn : (0 : ℝ) ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
    have hbase3 : (0 : ℝ) ≤ (N * R) / Mobs := by positivity
    have hbase4 : (0 : ℝ) ≤ (μ₀ * μ₁ * N * R * (β * logN)) / Mobs := by positivity
    rw [hΦ]
    have t1 : (0:ℝ) ≤ (μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 := by positivity
    have t2 : (0:ℝ) ≤ μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 := by positivity
    have t3 : (0:ℝ) ≤ Real.sqrt (β * logN) *
        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) := by
      have := Real.rpow_nonneg hbase3 ((3:ℝ)/2)
      positivity
    have t4 : (0:ℝ) ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hbase4 _
    linarith
  -- sample ratio lies in [0,1]
  have hpr := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  obtain ⟨hp0, hp1⟩ := hpr
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- decoupled three-copy bound at scale Cdec * Φ
  have hDec :
      bernoulliTripleEventProb p
          (fun Omega1 Omega2 Omega3 =>
            spectralNorm
              (quadraticNeumannAllDistinctDecoupledContribution
                Omega1 Omega2 Omega3 S p) ≤ Cdec * Φ) ≥
        1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := hDecoupled C' hCdec_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using this
  -- triple → diagonal coupling, generic threshold = Φ, failure = N^{-β}
  have hDiag :=
    hTriple S p Cdec cdec (Real.rpow (↑(max n₁ n₂)) (-β)) Φ
      hp0 hp1 hCdec hcdec hDec
  -- diagonal coupling → original contribution, generic bound = (K*Cdec)*Φ
  have hOrig :=
    quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail
      S p ((K * Cdec) * Φ)
      (1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β))
      hp0 hp1 hDiag
  -- weaken the bound from (K*Cdec)*Φ to (max Cdec (K*Cdec))*Φ via monotonicity
  have hweak : (K * Cdec) * Φ ≤ (max Cdec (K * Cdec)) * Φ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hΦnonneg
  have hMono :=
    bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
      (fun Omega =>
        spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          (K * Cdec) * Φ)
      (fun Omega =>
        spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          (max Cdec (K * Cdec)) * Φ)
      hp0 hp1 (fun Omega hΩ => le_trans hΩ hweak)
  have hFinal :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
              (max Cdec (K * Cdec)) * Φ) ≥
        1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    le_trans hOrig hMono
  simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using hFinal
