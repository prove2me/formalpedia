-- Prove2me | Theorems.Thm_finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- name    : finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T17:07:42.868528+00:00
-- url     : https://prove2.me/theorems/5b843ca2-91b0-4150-94b4-e7a7dbddffba
-- statement:
--   Finite-class Bousquet--Talagrand concentration for the Bernoulli empirical process used in Candès--Recht Appendix 9.1.
--
--   Let $p=m/(n_1n_2)$ and let $\Omega\subseteq \{1,\dots,n_1\}\times\{1,\dots,n_2\}$ be sampled by independent Bernoulli inclusion with probability $p$.  For a finite nonempty symmetric class of coefficient arrays $c_a(i,j)$, define
--   $$
--   Z(\Omega)=\max_a\sum_{i,j}\bigl(1_{(i,j)\in\Omega}-p\bigr)c_a(i,j).
--   $$
--   Assume the uniform increment bound $|c_a(i,j)|\le B$ and the variance proxy
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le \sigma^2
--   \quad\text{for every }a.
--   $$
--   The theorem asserts that there is a universal constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_p\left(|Z-\mathbb E_p Z|\le t\right)
--   \ge
--   1-3\exp\left(-{t\over KB}\log\left(1+{Bt\over \sigma^2+B\mathbb E_pZ}\right)\right).
--   $$
--
--   This is the finite-family maximum form of the product-space concentration theorem cited by Candès--Recht before applying it to the tangent-sampling supremum.  It is the genuine analytic core: the remaining Lean work should assemble the Bousquet/Talagrand modified-log-Sobolev and Herbst/ Chernoff ingredients into this finite empirical-process bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι =>
                ∑ i : Fin n₁, ∑ j : Fin n₂,
                  (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                    coeff a i j))
        bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Z))) := by sorry
