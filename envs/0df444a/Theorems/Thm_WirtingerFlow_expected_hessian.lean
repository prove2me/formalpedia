-- Prove2me | Theorems.Thm_WirtingerFlow_expected_hessian
-- name    : WirtingerFlow.expected_hessian
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T20:47:52.165729+00:00
-- url     : https://prove2.me/theorems/e63b5d0b-6bc9-44f0-b749-627de4dd6efa
-- title:
--   Lemma 7.1: expectation of the Hessian at the solution
-- statement:
--   Let $x\in\mathbb{C}^n$ with $\|x\|=1$, and let $f$ use the data $y_r=|a_r^*x|^2$. Each of the following holds entrywise:
--
--   1. If $a_1,\dots,a_m$ ($m\ge1$) follow the Gaussian model, then
--   $$\mathbb E[\nabla^2f(x)]=I_{2n}+\frac32\begin{bmatrix}x\\\bar x\end{bmatrix}[x^*,x^T]-\frac12\begin{bmatrix}x\\-\bar x\end{bmatrix}[x^*,-x^T].$$
--   2. The same identity holds in the coded diffraction model with $L\ge1$ patterns whose entries have an admissible law normalised by $\mathbb E|d|^2=1$. There the expectation is over the patterns.
--
--   This is the population Hessian at the solution, around which Lemma 7.4 concentrates the empirical Hessian.
--
--   **Formalization Note** The normalisation $\mathbb E|d|^2=1$ is not part of the paper's definition of admissibility, but the identity fails without it: scaling $d$ by $s$ scales the left side by $s^4$. The Gaussian case is proved in the paper through Lemmas A.1 and A.2. Lemma A.2 as printed has $\bar a_ra_r^*$ where $a_ra_r^T$ is meant.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Lemma 7.1, p. 20; Gaussian case via Lemmas A.1-A.2, Appendix A.1, p. 36

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem expected_hessian {n : ℕ} (x : Sig n) (hx : ‖x‖ = 1) :
    (∀ m : ℕ, 1 ≤ m → ∀ i j,
      ∫ A, hess (rows A) (meas (rows A) x) x i j ∂(gaussModel m n) = expHess x i j) ∧
    (∀ (ν : Measure ℂ) (M : ℝ), IsAdmissible ν M → ∫ d, ‖d‖ ^ 2 ∂ν = 1 →
      ∀ L : ℕ, 1 ≤ L → ∀ i j,
        ∫ d, hess (cdpVecs d) (meas (cdpVecs d) x) x i j ∂(cdpModel ν L n) = expHess x i j) := by sorry

end WirtingerFlow
