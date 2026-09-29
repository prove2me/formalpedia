-- Prove2me | solution 2 for quadratic_neumann_section63_first_index_distinct_centered_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:36:14.752389+00:00
-- url     : https://prove2.me/submissions/5ed108fd-9955-46f5-baad-e7ac36f9f4cb

import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32 and the p. 34 summary
display.  The centered part `S₁` of the `ω₁ ≠ ω₂ = ω₃` case after expanding
`ξ_{ω₂}^2 = (1 - 2p)ξ_{ω₂} + p(1-p)`, stated at the four-term §6.3 summary scale
`Φ` (Lemma 6.7 estimate).

Top-level assembly of the leaf
`quadratic_neumann_section63_first_index_distinct_centered_case_bound_under_general_sample_bound`:

* the genuine §6.3 analytic content is the two-copy *decoupled* estimate at the
  summary scale `Φ` (brick 1,
  `quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound`);
* it is transferred back to the original one-copy centered contribution using the
  general-sample (constant/`Φ`-scale) decoupling transfer (brick 2,
  `quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample`),
  which is itself the §6.3-summary-scale assembly of the two Proved generic
  transfers (pair → diagonal coupling, diagonal coupling → original).

This is the sound general-sample route: it carries `μ₁` explicitly via the
strong sample lower bound `m ≥ C'·max(max(μ₁²,√μ₀·μ₁), μ₀·N^{1/4})·N·r·β logN`
and uses the `min(n₁,n₂)` base estimate; it does NOT route through the deprecated
`lam`/`μ₀^{4/3}` max-denominator coefficient chain.
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
                (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
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
  -- brick 1: genuine §6.3 analytic content, the decoupled pair bound at scale Φ
  rcases
      quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound with
    ⟨Cpair, cpair, hCpair, hcpair, hPairBound⟩
  -- brick 2: general-sample (Φ-scale) pair → single decoupling transfer
  rcases
      quadratic_neumann_first_index_distinct_centered_decoupling_transfer_general_sample with
    ⟨Ctrans, ctrans, hCtrans, hctrans, hTransfer⟩
  refine ⟨max Cpair (Ctrans * Cpair), ctrans * cpair, ?_, by positivity, ?_⟩
  · exact lt_of_lt_of_le hCpair (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  -- abbreviate the §6.3 summary scale Φ
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
  have hCpair_le : Cpair ≤ C' := le_trans (le_max_left _ _) hC'
  have hKCpair_le : Ctrans * Cpair ≤ C' := le_trans (le_max_right _ _) hC'
  -- Φ ≥ 0 (each of the four summands is nonnegative)
  have hΦnonneg : 0 ≤ Φ := by
    have hNnat : 0 < max n₁ n₂ := Nat.lt_of_lt_of_le hn₁ (le_max_left _ _)
    have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hNnat
    have hRnn : (0 : ℝ) ≤ R := by rw [hR]; positivity
    have hMobsnn : (0 : ℝ) ≤ Mobs := by rw [hMobs]; positivity
    have hlogNnn : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
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
  -- sample ratio in [0,1]
  have hpr := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  obtain ⟨hp0, hp1⟩ := hpr
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- decoupled pair bound at scale Cpair * Φ
  have hPair :
      bernoulliPairEventProb p
          (fun Omega1 Omega2 =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                Omega1 Omega2 S p) ≤ Cpair * Φ) ≥
        1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := hPairBound C' hCpair_le β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using this
  -- pair → single via the general-sample (Φ-scale) decoupling transfer
  have hSingle :=
    hTransfer S p Cpair cpair β Φ hp0 hp1 hCpair hcpair hΦnonneg hPair
  -- weaken bound (Ctrans*Cpair)*Φ ≤ (max Cpair (Ctrans*Cpair))*Φ
  have hweak : (Ctrans * Cpair) * Φ ≤ (max Cpair (Ctrans * Cpair)) * Φ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hΦnonneg
  have hMono :=
    bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
      (fun Omega =>
        spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
          (Ctrans * Cpair) * Φ)
      (fun Omega =>
        spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
          (max Cpair (Ctrans * Cpair)) * Φ)
      hp0 hp1 (fun Omega hΩ => le_trans hΩ hweak)
  have hFinal :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
              (max Cpair (Ctrans * Cpair)) * Φ) ≥
        1 - (ctrans * cpair) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    le_trans hSingle hMono
  simpa only [hN, hR, hMobs, hlogN, hΦ, hp] using hFinal
