-- Prove2me | solution 1 for BanditAlgorithm.gittins_ae_discounted_value_interleaving_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T21:12:54.752566+00:00
-- url     : https://prove2.me/submissions/789bd4b9-a91b-401e-9a43-5bba11f7c53f

import Theorems.Thm_BanditAlgorithm_gittins_ae_certificates_of_greedy_charge_interleaving
import Theorems.Thm_BanditAlgorithm_tsum_chargeStackInterleaving_le_greedy

open MeasureTheory ProbabilityTheory ENNReal

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (hcal : ∀ (y : S) (ε : ℝ), 0 < ε →
      ∃ τ : (ℕ → S) → ℕ∞,
        BanditAlgorithm.IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        BanditAlgorithm.gittinsIndex P r α y - ε <
          (∫ ω, BanditAlgorithm.discountedStoppedSum α r τ ω
            ∂BanditAlgorithm.markovChainMeasure P y) /
            (∫ ω, BanditAlgorithm.discountedStoppedSum α (fun _ ↦ 1) τ ω
              ∂BanditAlgorithm.markovChainMeasure P y))
    (πstar : BanditAlgorithm.MarkovBanditPolicy k S)
    (hπ : BanditAlgorithm.IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (π : BanditAlgorithm.MarkovBanditPolicy k S) :
    ∃ μ : Measure
        ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))),
      ∀ ε : ℝ, 0 < ε →
        ∃ xs ys :
            ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))) →
              List ℝ,
          (∀ᵐ ω ∂μ, (xs ω).Perm (ys ω) ∧
            (ys ω).Pairwise (· ≥ ·)) ∧
          Integrable
            (fun ω ↦ (xs ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          Integrable
            (fun ω ↦ (ys ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          BanditAlgorithm.markovBanditDiscountedValue P r α π x ≤
            (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) + ε ∧
          (∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤
            BanditAlgorithm.markovBanditDiscountedValue P r α πstar x + ε := by
  apply BanditAlgorithm.gittins_ae_certificates_of_greedy_charge_interleaving
    P hr hα0 hα1 hint hcal πstar hπ x π
  intro H astar hH hastar a hsuma hsumg
  exact BanditAlgorithm.tsum_chargeStackInterleaving_le_greedy
    hH hastar hα0.le hα1.le a hsuma hsumg
