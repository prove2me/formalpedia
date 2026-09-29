-- Prove2me | solution 1 for KServer.randomized_yao_averaging
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:26:49.323888+00:00
-- url     : https://prove2.me/submissions/47f26073-af3d-45a6-aae1-cd44607b75f4

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

open KServer MeasureTheory

private theorem cost_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (A : OnlineAlgorithm k M) (σ : List M) : 0 ≤ A.cost σ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

private theorem offlineCost_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

/-- **The easy direction of Yao's principle** for mixed-strategy randomized k-server
algorithms: a competitive randomized algorithm contains, for every finitely supported
distribution over request sequences and every slack `ε > 0`, a deterministic algorithm
in its support whose average cost is within `ε` of the competitive bound in average. -/
theorem solution (k : ℕ) (M : Type*) [MetricSpace M]
    (A : RandomizedAlgorithm k M) (C₀ : Config k M) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : A.IsCompetitiveFrom C₀ ρ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ (m : ℕ) (p : Fin m → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 →
      ∀ (σ : Fin m → List M) (ε : ℝ), 0 < ε →
        ∃ i : A.ι, (A.alg i).conf [] = C₀ ∧
          ∑ j, p j * (A.alg i).cost (σ j)
            ≤ ρ * (∑ j, p j * offlineCost C₀ (σ j)) + a + ε := by
  classical
  obtain ⟨hconf, a, ha⟩ := hA
  refine ⟨max a 0, le_max_right a 0, ?_⟩
  intro m p hp0 hp1 σ ε hε
  by_contra hcon
  push_neg at hcon
  haveI := A.prob
  set B : ℝ := ρ * (∑ j, p j * offlineCost C₀ (σ j)) + max a 0 with hB
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ ∑ j, p j * offlineCost C₀ (σ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (offlineCost_nonneg C₀ (σ j))
    have h2 := mul_nonneg hρ h1
    rw [hB]
    have h3 := le_max_right a 0
    linarith
  -- every outcome pays more than `B + ε` on average
  have hpt : ∀ i : A.ι, ENNReal.ofReal (B + ε)
      ≤ ENNReal.ofReal (∑ j, p j * (A.alg i).cost (σ j)) := by
    intro i
    refine ENNReal.ofReal_le_ofReal (le_of_lt ?_)
    have h := hcon i (hconf i)
    rw [hB]
    linarith
  -- integrate the pointwise bound
  have hlow : ENNReal.ofReal (B + ε)
      ≤ ∫⁻ i, ENNReal.ofReal (∑ j, p j * (A.alg i).cost (σ j)) ∂A.μ := by
    calc ENNReal.ofReal (B + ε)
        = ∫⁻ _, ENNReal.ofReal (B + ε) ∂A.μ := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono hpt
  -- linearity of the lower integral over the finite average
  have hlin : (∫⁻ i, ENNReal.ofReal (∑ j, p j * (A.alg i).cost (σ j)) ∂A.μ)
      = ∑ j, ENNReal.ofReal (p j) * A.expCost (σ j) := by
    have hstep : ∀ i : A.ι, ENNReal.ofReal (∑ j, p j * (A.alg i).cost (σ j))
        = ∑ j, ENNReal.ofReal (p j) * ENNReal.ofReal ((A.alg i).cost (σ j)) := by
      intro i
      rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hp0 j) (cost_nonneg _ _)]
      exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (hp0 j)
    calc (∫⁻ i, ENNReal.ofReal (∑ j, p j * (A.alg i).cost (σ j)) ∂A.μ)
        = ∫⁻ i, ∑ j, ENNReal.ofReal (p j) * ENNReal.ofReal ((A.alg i).cost (σ j)) ∂A.μ :=
          lintegral_congr hstep
      _ = ∑ j, ∫⁻ i, ENNReal.ofReal (p j) * ENNReal.ofReal ((A.alg i).cost (σ j)) ∂A.μ :=
          lintegral_finset_sum _ fun j _ => ((A.meas (σ j)).ennreal_ofReal).const_mul _
      _ = ∑ j, ENNReal.ofReal (p j) * A.expCost (σ j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_const_mul _ ((A.meas (σ j)).ennreal_ofReal)]
          rfl
  -- competitiveness bounds the average expected cost by `B`
  have hup : (∑ j, ENNReal.ofReal (p j) * A.expCost (σ j)) ≤ ENNReal.ofReal B := by
    have hstep : ∀ j : Fin m, ENNReal.ofReal (p j) * A.expCost (σ j)
        ≤ ENNReal.ofReal (p j * (ρ * offlineCost C₀ (σ j) + max a 0)) := by
      intro j
      have h1 : A.expCost (σ j)
          ≤ ENNReal.ofReal (ρ * offlineCost C₀ (σ j) + max a 0) := by
        refine le_trans (ha (σ j)) (ENNReal.ofReal_le_ofReal ?_)
        have h2 := le_max_left a 0
        linarith
      calc ENNReal.ofReal (p j) * A.expCost (σ j)
          ≤ ENNReal.ofReal (p j) * ENNReal.ofReal (ρ * offlineCost C₀ (σ j) + max a 0) :=
            mul_le_mul_left' h1 _
        _ = ENNReal.ofReal (p j * (ρ * offlineCost C₀ (σ j) + max a 0)) :=
            (ENNReal.ofReal_mul (hp0 j)).symm
    calc (∑ j, ENNReal.ofReal (p j) * A.expCost (σ j))
        ≤ ∑ j, ENNReal.ofReal (p j * (ρ * offlineCost C₀ (σ j) + max a 0)) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = ENNReal.ofReal (∑ j, p j * (ρ * offlineCost C₀ (σ j) + max a 0)) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hp0 j)
            (add_nonneg (mul_nonneg hρ (offlineCost_nonneg C₀ (σ j)))
              (le_max_right a 0))).symm
      _ = ENNReal.ofReal B := by
          congr 1
          have hsplit : ∀ j : Fin m, p j * (ρ * offlineCost C₀ (σ j) + max a 0)
              = ρ * (p j * offlineCost C₀ (σ j)) + p j * max a 0 := fun j => by ring
          rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.sum_mul, hp1, one_mul, hB]
  have hfinal : ENNReal.ofReal (B + ε) ≤ ENNReal.ofReal B := by
    calc ENNReal.ofReal (B + ε) ≤ _ := hlow
      _ = _ := hlin
      _ ≤ _ := hup
  rw [ENNReal.ofReal_le_ofReal_iff hB0] at hfinal
  linarith
