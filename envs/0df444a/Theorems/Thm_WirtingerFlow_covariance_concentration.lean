-- Prove2me | Theorems.Thm_WirtingerFlow_covariance_concentration
-- name    : WirtingerFlow.covariance_concentration
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:33:58.511662+00:00
-- url     : https://prove2.me/theorems/4b52f519-e1bc-4e8e-aa56-6b9470a9bcda
-- title:
--   Lemma 7.8: concentration of the sample covariance matrix
-- statement:
--   1. **Gaussian model.** For every $\delta>0$ there are constants $c(\delta)>0$ and $\gamma>0$ such that, whenever $n\ge1$ and $m\ge c(\delta)\,n\log n$, with probability at least $1-2e^{-\gamma m}$,
--   $$\Big\|I_n-\frac1m\sum_{r=1}^ma_ra_r^*\Big\|\le\delta,$$
--   and on this event
--   $$(1-\delta)\|h\|^2\le\frac1m\sum_{r=1}^m|a_r^*h|^2\le(1+\delta)\|h\|^2\quad\text{for all }h\in\mathbb{C}^n.$$
--   2. **Coded diffraction model.** For every $\delta>0$ and every bound $M$ there is a constant $c(\delta)>0$ such that, for every admissible law with bound $M$ and $\mathbb E|d|^2=1$, whenever $n,L\ge1$ and $L\ge c(\delta)\log^3n$, the same two conclusions hold (with $m=nL$) with probability at least $1-1/n^2$.
--
--   **Formalization Note** $\gamma$ is allowed to depend on $\delta$. A constant $\gamma$ that works for every $\delta$ does not exist: $\frac1m\sum_r|a_r(1)|^2$ is a Gamma$(m,1)/m$ variable, which deviates from $1$ by more than $\delta$ with probability of order $e^{-m\delta^2/2}$. That exceeds $2e^{-\gamma m}$ once $\delta^2<2\gamma$, for $m$ large.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Lemma 7.8, eq. (7.9), p. 22; proof in Appendix A.8, p. 41

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem covariance_concentration :
    (∀ δ : ℝ, 0 < δ → ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → c * n * Real.log n ≤ m →
        gaussModel m n {A | ¬ (opNorm (1 - covMat (rows A)) ≤ δ ∧
          ∀ h : Sig n, (1 - δ) * ‖h‖ ^ 2 ≤ 1 / (m : ℝ) * ∑ r, ‖inner ℂ (rows A r) h‖ ^ 2 ∧
            1 / (m : ℝ) * ∑ r, ‖inner ℂ (rows A r) h‖ ^ 2 ≤ (1 + δ) * ‖h‖ ^ 2)} ≤
          ENNReal.ofReal (2 * Real.exp (-γ * m))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ c : ℝ, 0 < c ∧
      ∀ ν : Measure ℂ, IsAdmissible ν M → ∫ d, ‖d‖ ^ 2 ∂ν = 1 →
      ∀ n L : ℕ, 1 ≤ n → 1 ≤ L → c * Real.log n ^ 3 ≤ L →
        cdpModel ν L n {d | ¬ (opNorm (1 - covMat (cdpVecs d)) ≤ δ ∧
          ∀ h : Sig n, (1 - δ) * ‖h‖ ^ 2 ≤
              1 / ((L * n : ℕ) : ℝ) * ∑ r, ‖inner ℂ (cdpVecs d r) h‖ ^ 2 ∧
            1 / ((L * n : ℕ) : ℝ) * ∑ r, ‖inner ℂ (cdpVecs d r) h‖ ^ 2 ≤ (1 + δ) * ‖h‖ ^ 2)} ≤
          ENNReal.ofReal (1 / (n : ℝ) ^ 2)) := by sorry

end WirtingerFlow
