-- Prove2me | solution 2 for scalar_centered_sampling_bernstein_natural_tail_from_quadratic_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:29:52.500792+00:00
-- url     : https://prove2.me/submissions/ed89ee13-ca78-42c1-84a9-5df695c602d1

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_quadratic_base_scalar_bernstein_natural_scale_absorption

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

namespace Prove53b0

variable {n₁ n₂ : ℕ}

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- Event probability is monotone in the threshold: if `A ≤ B`, then
`P(|Z| ≤ A) ≤ P(|Z| ≤ B)` (the smaller-threshold event is contained in the
larger). -/
theorem event_prob_threshold_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (A B : ℝ) (hAB : A ≤ B) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ A) ≤
      bernoulliEventProb p (fun Omega => |Z Omega| ≤ B) := by
  classical
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : |Z Omega| ≤ A
  · have hB : |Z Omega| ≤ B := le_trans hA hAB
    simp only [hA, hB, if_true, le_refl]
  · by_cases hB : |Z Omega| ≤ B
    · simp only [hA, hB, if_true, if_false]
      exact weight_nonneg p hp0 hp1 Omega
    · simp only [hA, hB, if_false, le_refl]

end Prove53b0

open Prove53b0 in
/-- `scalar_centered_sampling_bernstein_natural_tail_from_quadratic_base_bounds`
(53b03e2d) as a reduction onto the general scalar Bernstein tail
`scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales` (3cbb6b11)
and the deterministic scale-absorption node
`quadratic_base_scalar_bernstein_natural_scale_absorption` (f4c4f764). -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm B ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                Cpoint *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  -- general scalar Bernstein tail constants
  obtain ⟨Cbern, cbern, hCbern, hcbern, htail⟩ :=
    scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
  -- deterministic absorption: choose Cpoint
  obtain ⟨Cpoint, hCpoint, habs⟩ :=
    quadratic_base_scalar_bernstein_natural_scale_absorption Cbern Centry Cfro
      hCbern hCentry hCfro
  refine ⟨Cpoint, cbern, hCpoint, hcbern, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn1 hn2 hr hmle hμ₀ hsample Coeff B hCoeff hentry hfrob
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  -- entryScale, frobScale = quadratic-base bounds
  set entryScale : ℝ := Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) with hes
  set frobScale : ℝ := Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
      Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) with hfs
  -- the general tail at these scales
  have htail' := htail β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  -- the deterministic absorption bound
  have habs' := habs β lam hβ hlam n₁ n₂ r m μ₀ hn1 hn2 hr hmle hμ₀ hsample
  -- absorption gives:  Cbern * (...) ≤ Cpoint * lam^{-1/2}
  -- threshold monotonicity transfers the tail to the absorbed threshold
  set A : ℝ := Cbern *
      (Real.sqrt ((β * Real.log (↑(max n₁ n₂))) / p) * frobScale +
        ((β * Real.log (↑(max n₁ n₂))) / p) * entryScale) with hA
  set Bnd : ℝ := Cpoint *
      Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
        Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2) with hBnd
  have hAB : A ≤ Bnd := by
    rw [hA, hBnd, hp, hes, hfs] at *
    exact habs'
  have hmono := event_prob_threshold_mono (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Coeff A Bnd hAB
  -- chain: P(|Coeff| ≤ Bnd) ≥ P(|Coeff| ≤ A) ≥ 1 - cbern * n^{-β}
  have : bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ A) ≥
      1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := htail'
  calc 1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β)
      ≤ bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ A) := this
    _ ≤ bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ Bnd) := hmono
