-- Prove2me | Theorems.Thm_WirtingerFlow_expected_gradient
-- name    : WirtingerFlow.expected_gradient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T20:57:10.071294+00:00
-- url     : https://prove2.me/theorems/983e60ce-ba1e-47bf-810a-2d3ab7b17a88
-- title:
--   Lemma 7.2: expectation of the Wirtinger gradient
-- statement:
--   Let $x\in\mathbb{C}^n$ with $\|x\|=1$, let $z\in\mathbb{C}^n$ be fixed, and let $f$ use the data $y_r=|a_r^*x|^2$. In the Gaussian model with $m\ge1$ samples, and in the coded diffraction model with $L\ge1$ patterns of admissible law with $\mathbb E|d|^2=1$,
--
--   $$\mathbb E[\nabla f(z)]=(I-xx^*)z+2\big(\|z\|^2-1\big)z.$$
--
--   In expectation, Wirtinger flow is therefore gradient descent on a function whose minimisers are the vectors $e^{i\varphi}x$.
--
--   **Formalization Note** The expectation of the vector $\nabla f(z)$ is a Bochner integral in $\mathbb{C}^n$. The normalisation $\mathbb E|d|^2=1$ is made explicit as in Lemma 7.1.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Lemma 7.2, p. 20; proof in Appendix A.2, p. 36

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem expected_gradient {n : ℕ} (x : Sig n) (hx : ‖x‖ = 1) (z : Sig n) :
    (∀ m : ℕ, 1 ≤ m →
      ∫ A, grad (rows A) (meas (rows A) x) z ∂(gaussModel m n) =
        z - inner ℂ x z • x + ((2 * (‖z‖ ^ 2 - 1) : ℝ) : ℂ) • z) ∧
    (∀ (ν : Measure ℂ) (M : ℝ), IsAdmissible ν M → ∫ d, ‖d‖ ^ 2 ∂ν = 1 →
      ∀ L : ℕ, 1 ≤ L →
        ∫ d, grad (cdpVecs d) (meas (cdpVecs d) x) z ∂(cdpModel ν L n) =
          z - inner ℂ x z • x + ((2 * (‖z‖ ^ 2 - 1) : ℝ) : ℂ) • z) := by sorry

end WirtingerFlow
