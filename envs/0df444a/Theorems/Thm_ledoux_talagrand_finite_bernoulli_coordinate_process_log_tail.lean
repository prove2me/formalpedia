-- Prove2me | Theorems.Thm_ledoux_talagrand_finite_bernoulli_coordinate_process_log_tail
-- name    : ledoux_talagrand_finite_bernoulli_coordinate_process_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T20:10:44.691432+00:00
-- url     : https://prove2.me/theorems/43f51d1d-58eb-4964-acf9-b7c8126628c3
-- statement:
--   This is the finite Bernoulli-coordinate specialization of the textbook Talagrand--Ledoux concentration theorem for bounded centered empirical-process suprema.
--
--   Let $\Omega\subseteq [n_1]\times[n_2]$ be sampled in the independent Bernoulli model with
--   $$
--   p=\frac{m}{n_1n_2}.
--   $$
--   For each element $a$ of a finite nonempty index class, let $c_a(i,j)$ be a real coefficient array and define the centered coordinate sum
--   $$
--   S_a(\Omega)=\sum_{i,j}\bigl(1_{(i,j)\in\Omega}-p\bigr)c_a(i,j).
--   $$
--   Set
--   $$
--   Z(\Omega)=\max_a S_a(\Omega),\qquad
--   \bar Z(\Omega)=\max_a |S_a(\Omega)|.
--   $$
--   Assume the uniform envelope bound
--   $$
--   |c_a(i,j)|\le B\quad\text{for all }a,i,j,
--   $$
--   with $B>0$, and the Bernoulli variance proxy bound
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le \sigma^2
--   \quad\text{for every }a.
--   $$
--   Then there is a universal numerical constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_p\left(|Z-\mathbb E_p Z|\le t\right)
--   \ge
--   1-3\exp\left(
--   -{t\over KB}\log\left(1+{Bt\over \sigma^2+B\mathbb E_p\bar Z}\right)
--   \right).
--   $$
--
--   This node is intended as the textbook terminal analytic input for the Candès--Recht Appendix 9.1 Talagrand step. The absolute supremum $\bar Z$ is kept because this is the standard non-symmetric empirical-process form; the symmetric Candès--Recht specialization is obtained by the elementary identity $\bar Z=Z$ when the coefficient class is closed under $c\mapsto -c$.
--
--   Source location: Ledoux, *The Concentration of Measure Phenomenon*, Section 7, Corollary 7.8. The equivalent local lecture-note statement is Ledoux, Section 3.4, Theorem 3.6 plus the following paragraph stating that the same bound controls $\mathbb P\{|Z-\mathbb E Z|\ge r\}$ up to numerical constants. Candès--Romberg, PDF p. 11, Theorem 3.2, cites this Ledoux corollary before applying it to Bernoulli coordinate sampling; Candès--Recht Appendix 9.1, PDF p. 46, invokes the symmetric form as Theorem 9.1.
-- source:
--   Ledoux, Michel. The Concentration of Measure Phenomenon. American Mathematical Society, 2001, Section 7, Corollary 7.8; finite Bernoulli-coordinate specialization used in Candes-Recht Appendix 9.1.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem ledoux_talagrand_finite_bernoulli_coordinate_process_log_tail :
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
