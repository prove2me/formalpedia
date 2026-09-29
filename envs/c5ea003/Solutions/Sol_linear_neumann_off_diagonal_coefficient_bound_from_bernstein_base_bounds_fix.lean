-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds_fix
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-25T02:17:38.270964+00:00
-- url     : https://prove2.me/submissions/4b02701e-64e5-4805-842a-e834bd21aa02

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_shifted_pointwise_tails
import Theorems.Thm_linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open Real MatrixCompletion

set_option maxHeartbeats 1000000

/-- **CR-faithful corrected off-diagonal first-Neumann coefficient Bernstein bound.**
Same as `linear_neumann_off_diagonal_coefficient_bound_from_bernstein_base_bounds` but
with the μ₀-linear sample lower bound `max μ₀ μ₁` (CR2009 Lemma 6.6 eq 6.15:
`np ≥ 4β√3 μ₀ r log n`; Thm 1.3 eq 1.9 `max(μ₁²,μ₀μ₁,μ₀ n^{1/4})`).  The reduction:
per-cell raw two-term Bernstein tail (`pointwise`, self-calibrating, sound) → union over
`n₁n₂` cells (`uniform_two_term`) → absorb the raw threshold into the clean scale
(`absorbed_..._fix`, the μ₀-linear correction) via event monotonicity
(`bernoulli_event_probability_mono`). -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max μ₀ μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w : Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        (∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) →
        (∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  -- constants from children
  obtain ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩ :=
    linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
      Centry Cfro hCentry hCfro
  obtain ⟨Ctwo, ctwo, hCtwo, hctwo, hunif⟩ :=
    linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_shifted_pointwise_tails
      Cpoint cpoint Centry Cfro hCpoint hcpoint
  obtain ⟨Cabs, hCabs, habs⟩ :=
    linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
      Ctwo Centry Cfro hCtwo hCentry hCfro
  refine ⟨Cabs, ctwo, hCabs, hctwo, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hmN hμ₀ hμ₁ hA0 hA1
    hsample hrepr hentry hfro
  -- the corrected sample bound (max μ₀ μ₁) implies the √μ₀ sample bound the sound children need
  have hsqrtle : Real.sqrt μ₀ ≤ μ₀ := by
    calc Real.sqrt μ₀ ≤ Real.sqrt (μ₀ * μ₀) := by
            apply Real.sqrt_le_sqrt; nlinarith [hμ₀]
      _ = μ₀ := by rw [Real.sqrt_mul_self (le_of_lt (lt_of_lt_of_le one_pos hμ₀))]
  have hsample_sqrt : (m : ℝ) ≥
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
        (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by
    refine le_trans ?_ hsample
    gcongr
  -- p ∈ [0,1]
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hmN
  -- (1) per-cell raw tails (pointwise), uniformized
  have huniform_in : ∀ w : Fin n₁ × Fin n₂,
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
                      Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
                  (((β + 2) * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Centry * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))))) ≥
        1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w
    exact hpoint β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hmN hμ₀ hμ₁ hA0 hA1
      hsample_sqrt w (fun Omega2 => hrepr Omega2 w) (hentry w) (hfro w)
  have huniform :=
    hunif β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hmN hμ₀ hμ₁ hA0 hA1
      hsample_sqrt huniform_in
  -- (2) absorption: raw two-term threshold ≤ Cabs * clean scale
  have habsorb := habs β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hmN hμ₀ hμ₁ hsample
  -- (3) event monotonicity: {coeffBound ≤ Ctwo*raw} ⊆ {coeffBound ≤ Ctwo*Cabs*clean}
  set rawThresh : ℝ :=
      Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
        (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) with hrawdef
  set cleanScale : ℝ :=
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
      with hcleandef
  -- habsorb : Ctwo * rawThresh ≤ Cabs * cleanScale  (as written by the absorption node)
  have habsorb' : Ctwo * rawThresh ≤ Cabs * cleanScale := by
    -- habsorb (the corrected-leaf node): Ctwo*rawThresh ≤ Cabs*μ₁*√(r/N)*√clean.
    have hclean_eq : Cabs * cleanScale
        = Cabs * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
      rw [hcleandef]; ring
    rw [hclean_eq, hrawdef]
    exact habsorb
  -- monotone transfer
  have hmono := bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega2 => LinearNeumannOffDiagonalCoefficientBound Omega2 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (Ctwo * rawThresh))
      (fun Omega2 => LinearNeumannOffDiagonalCoefficientBound Omega2 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (Cabs * cleanScale))
      hp0 hp1
      (by
        intro Omega2 hev
        -- hev : entrySupNorm ≤ Ctwo*rawThresh ;  want ≤ (Ctwo*Cabs)*cleanScale
        unfold LinearNeumannOffDiagonalCoefficientBound at hev ⊢
        exact le_trans hev habsorb')
  -- assemble: rewrite goal scale = (Ctwo*Cabs)*cleanScale and the uniform conclusion = Ctwo*rawThresh
  have hgoal_scale : Cabs * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
      = Cabs * cleanScale := by rw [hcleandef]; ring
  rw [hgoal_scale]
  -- uniform's conclusion bound = Ctwo * rawThresh (definitionally, by hrawdef)
  have huniform' : bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega2 => LinearNeumannOffDiagonalCoefficientBound Omega2 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (Ctwo * rawThresh))
        ≥ 1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have : (Ctwo *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Cfro * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
                (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  (Centry * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))))
        = Ctwo * rawThresh := by rw [hrawdef]
    rw [← this]; exact huniform
  -- chain: goal prob ≥ uniform prob ≥ 1 - ctwo n^{-β}
  exact le_trans huniform' hmono
