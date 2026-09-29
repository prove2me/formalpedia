-- Prove2me | Theorems.Thm_candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail
-- name    : candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T17:59:33.441609+00:00
-- url     : https://prove2.me/theorems/18e3c356-a6c1-4063-b927-1f7c60cae5e9
-- statement:
--   This is the finite Bernoulli-coordinate specialization of the Talagrand empirical-process concentration theorem stated as Candès--Romberg, Theorem 3.2, and cited by Candès--Recht Appendix 9.1.
--
--   Let $\Omega\subseteq [n_1]	imes[n_2]$ be sampled in the independent Bernoulli model with
--   $$
--   p=rac{m}{n_1n_2}.
--   $$
--   For a finite nonempty class of coefficient arrays $c_a(i,j)$ define the centered coordinate process
--   $$
--   S_a(\Omega)=\sum_{i,j}igl(1_{(i,j)\in\Omega}-pigr)c_a(i,j),
--   $$
--   and set
--   $$
--   Z(\Omega)=\max_a S_a(\Omega),\qquad
--   ar Z(\Omega)=\max_a |S_a(\Omega)|.
--   $$
--   Assume the uniform envelope bound
--   $$
--   |c_a(i,j)|\le B
--   $$
--   and the variance proxy bound
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le \sigma^2
--   \quad	ext{for every }a.
--   $$
--   Then there is a universal numerical constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_pigl(|Z-\mathbb E_p Z|\le tigr)
--   \ge
--   1-3\exp\left(
--   -{t\over K B}\log\left(1+{B t\over \sigma^2+B\mathbb E_par Z}ight)
--   ight).
--   $$
--
--   This statement deliberately keeps the $ar Z$ denominator appearing in Candès--Romberg Theorem 3.2. The existing Candès--Recht Appendix 9.1 finite-max leaf is the symmetric-class specialization, where closure under $c\mapsto -c$ makes $ar Z=Z$.
--
--   Source location: Candès--Romberg, "Sparsity and incoherence in compressive sampling", PDF p. 11, Theorem 3.2 and equation (3.9). Candès--Recht Appendix 9.1, PDF p. 46, says its Theorem 4.2 proof follows this argument and restates the same Talagrand input as Theorem 9.1.
-- source:
--   Candès, Emmanuel, and Justin Romberg. "Sparsity and incoherence in compressive sampling." Inverse Problems 23.3 (2007): 969-985, Theorem 3.2; cited by Candès and Recht, "Exact matrix completion via convex optimization," Appendix 9.1.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun a Omega =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j)
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
        let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι => |process a Omega|)
        bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  sorry
