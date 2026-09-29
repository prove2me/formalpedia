-- Prove2me | solution 1 for BanditAlgorithm.exp4_estimate_advantage_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:15:14.77986+00:00
-- url     : https://prove2.me/submissions/05581972-0349-4db9-9cf1-8ca8e293ea6f

import Theorems.Thm_BanditAlgorithm_exp4_expected_potential_bound
import Theorems.Thm_BanditAlgorithm_exp4_mixture_estimate_expectation_eq_reward
import Theorems.Thm_BanditAlgorithm_exp4_quadratic_mass_expectation_bound

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 18.1 proof, printed
p. 230.  The imported potential inequality is Lemma 18.2 / Eq. (18.9);
the mixture-score identity is the conditional-expectation calculation around
Eq. (18.10); and the quadratic-mass estimate is Eq. (18.12).
-/

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, exp4Estimate η 0 E n h m ∂(adversarialMeasure x π n)) -
        (∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n)) ≤
      Real.log M / η + η * ((n : ℝ) * k) / 2 := by
  have hpotential :=
    exp4_expected_potential_bound
      hk hM n hn η hη x hx E hE0 hE1 π hπ m
  have hmixture :=
    exp4_mixture_estimate_expectation_eq_reward
      hk hM n hn η hη x hx E hE0 hE1 π hπ
  have hquadratic :=
    exp4_quadratic_mass_expectation_bound
      hk hM n hn η hη x hx E hE0 hE1 π hπ
  rw [hmixture] at hpotential
  have hscaled := mul_le_mul_of_nonneg_left hquadratic
    (show 0 ≤ η / 2 by positivity)
  nlinarith
