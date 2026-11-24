-- Prove2me | Theorems.Thm_WirtingerFlow_hessian_concentration
-- name    : WirtingerFlow.hessian_concentration
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:16:10.896046+00:00
-- url     : https://prove2.me/theorems/4df7e183-35e0-4b4f-b4a0-66f898b7655f
-- title:
--   Lemma 7.4: concentration of the Hessian at the solution
-- statement:
--   Let $x\in\mathbb{C}^n$ with $\|x\|=1$, and let $f$ use the data $y_r=|a_r^*x|^2$.
--
--   1. **Gaussian model.** For every $\delta>0$ there are constants $c(\delta)>0$ and $\gamma>0$ such that, whenever $n\ge1$ and $m\ge c(\delta)\,n\log n$,
--   $$\big\|\nabla^2f(x)-\mathbb E[\nabla^2f(x)]\big\|\le\delta$$
--   with probability at least $1-10e^{-\gamma n}-8/n^2$.
--   2. **Coded diffraction model.** For every $\delta>0$ and every bound $M$ there is a constant $c(\delta)>0$ such that, for every admissible law with bound $M$ and $\mathbb E|d|^2=1$, whenever $n,L\ge1$ and $L\ge c(\delta)\log^3n$, the same inequality holds with probability at least $1-(2L+1)/n^3$.
--
--   Here $\mathbb E[\nabla^2f(x)]$ is the matrix of Lemma 7.1 and $\|\cdot\|$ is the operator norm.
--
--   **Formalization Note** The paper does not say whether $\gamma$ may depend on $\delta$, or whether $c(\delta)$ may depend on the bound $M$ of the admissible law. The statement allows both dependences. A failure probability is stated as an upper bound on the (outer) probability of the set of samples where the inequality fails, which is the same as the existence of an event of the stated probability on which it holds.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Lemma 7.4, p. 21; proof in Appendix A.4, pp. 37-39

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem hessian_concentration :
    (∀ δ : ℝ, 0 < δ → ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → c * n * Real.log n ≤ m → ∀ x : Sig n, ‖x‖ = 1 →
        gaussModel m n {A | ¬ opNorm (hess (rows A) (meas (rows A) x) x - expHess x) ≤ δ} ≤
          ENNReal.ofReal (10 * Real.exp (-γ * n) + 8 / (n : ℝ) ^ 2)) ∧
    (∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∃ c : ℝ, 0 < c ∧
      ∀ ν : Measure ℂ, IsAdmissible ν M → ∫ d, ‖d‖ ^ 2 ∂ν = 1 →
      ∀ n L : ℕ, 1 ≤ n → 1 ≤ L → c * Real.log n ^ 3 ≤ L → ∀ x : Sig n, ‖x‖ = 1 →
        cdpModel ν L n {d | ¬ opNorm (hess (cdpVecs d) (meas (cdpVecs d) x) x - expHess x) ≤ δ} ≤
          ENNReal.ofReal ((2 * L + 1) / (n : ℝ) ^ 3)) := by sorry

end WirtingerFlow
