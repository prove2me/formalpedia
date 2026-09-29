-- Prove2me | Theorems.Thm_BanditAlgorithm_le_of_ae_discounted_permutation_approximations
-- name    : BanditAlgorithm.le_of_ae_discounted_permutation_approximations
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:47:45.354921+00:00
-- url     : https://prove2.me/theorems/06c05253-f687-4ce9-a502-46509d7bd383
-- title:
--   Expected dominance from almost-sure discounted interleavings
-- statement:
--   Let random finite charge lists $X_\varepsilon$ and $Y_\varepsilon$ be available for every $\varepsilon>0$. Assume almost surely that $X_\varepsilon$ is a permutation of $Y_\varepsilon$ and that $Y_\varepsilon$ is nonincreasing. If their discounted values are integrable and approximate $u$ from below and $v$ from above in expectation, respectively, then $u\leq v$.
--
--   This is the expectation-and-limit form of the deterministic discounted interleaving inequality used for random reward stacks.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 35.9, Part 2 on printed pp.452--453, applying Lemma 35.10 pathwise to the random prevailing-charge stacks and then taking expectations.

import Theorems.Thm_BanditAlgorithm_discounted_list_value_le_of_perm_pairwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

theorem BanditAlgorithm.le_of_ae_discounted_permutation_approximations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert : ∀ ε : ℝ, 0 < ε →
      ∃ xs ys : Ω → List ℝ,
        (∀ᵐ ω ∂μ, (xs ω).Perm (ys ω) ∧
          (ys ω).Pairwise (· ≥ ·)) ∧
        Integrable (fun ω ↦ (xs ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
        Integrable (fun ω ↦ (ys ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
        u ≤ (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) + ε ∧
        (∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤ v + ε) :
    u ≤ v := by
  sorry
