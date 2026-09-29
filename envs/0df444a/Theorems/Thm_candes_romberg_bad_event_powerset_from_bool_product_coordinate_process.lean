-- Prove2me | Theorems.Thm_candes_romberg_bad_event_powerset_from_bool_product_coordinate_process
-- name    : candes_romberg_bad_event_powerset_from_bool_product_coordinate_process
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T02:47:59.289168+00:00
-- url     : https://prove2.me/theorems/e707af12-5f1c-4abc-8a72-0ead43fdc63e
-- statement:
--   Formal bridge from the Boolean product-measure version of the Candes--Romberg Talagrand bad-event theorem to the existing powerset `bernoulliEventProb` formulation used by `candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail`.
--
--   Source-backed child/parent route: the analytic input is Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Theorem 3.2, equation (3.9), cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2). The probability-model bridge uses the Bernoulli sampling model in Candes--Recht PDF p. 18, Section 4.1, equations (4.3)--(4.4).
--
--   Mathematical statement and notation: let $p=m/(n_1n_2)$ and let $\Omega\subseteq [n_1]\times[n_2]$ be sampled in the independent Bernoulli model. For a finite nonempty coefficient class $c_a(i,j)$, define
--   $$
--   S_a(\Omega)=\sum_{i,j}(1_{(i,j)\in\Omega}-p)c_a(i,j),\quad
--   Z(\Omega)=\max_a S_a(\Omega),\quad
--   \bar Z(\Omega)=\max_a |S_a(\Omega)|.
--   $$
--   The Boolean product-measure child states the same inequality over samples $\omega: [n_1]\times[n_2]\to\{0,1\}$ with probability measure $\mathrm{bernMeasure}(p)$, and this bridge transfers it to the powerset expression
--   $$
--   \mathbb P_p\{|Z-\mathbb E_pZ|>t\}
--   \le
--   3\exp\!\left(-{t\over KB}\log\left(1+{Bt\over \sigma^2+B\mathbb E_p\bar Z}\right)\right).
--   $$
--   Here $B>0$ is the envelope bound $|c_a(i,j)|\le B$, and $\sigma^2$ is the variance proxy satisfying
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le\sigma^2.
--   $$
--   The coherence parameters $\mu_0,\mu_1$ and `successProb` do not appear in this external concentration bridge.
--
--   Formalization note: this is a formal bridge, not a theorem appearing verbatim in the paper and not a new analytic concentration proof. It bridges a source-backed Boolean product-measure child to the source-backed powerset child `candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail`. The Lean proof should only package the sample ratio as `NNReal` using `sample_ratio_between_zero_and_one`, rewrite event probabilities via `bernoulli_powerset_event_prob_eq_product_measure`, rewrite both expectations via `bernoulli_powerset_expectation_eq_product_measure_integral`, and use the identity between `indicatorToFinset` samples and the powerset process.
-- source:
--   Formal bridge. The source-backed analytic child is Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Theorem 3.2, equation (3.9), cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2). The Bernoulli model bridge is Candes--Recht PDF p. 18, Section 4.1, equations (4.3)--(4.4).

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_bernoulli_measure
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_powerset_event_prob_eq_product_measure
import Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem candes_romberg_bad_event_powerset_from_bool_product_coordinate_process
    (hProduct :
      ∃ K : ℝ, 0 < K ∧
        ∀ (n₁ n₂ : ℕ) (p : NNReal) (hp : p ≤ 1)
          (ι : Type) [Fintype ι] [Nonempty ι]
          (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
          0 < B → 0 ≤ sigmaSq → 0 ≤ t →
          (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B) →
          (∀ a : ι,
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
          let boolProcess : ι → ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
            fun a ω =>
              ∑ i : Fin n₁, ∑ j : Fin n₂,
                ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
          let boolZ : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
            fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
          let boolZbar : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
            fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
          (bernMeasure (n1 := n₁) (n2 := n₂) p hp).real
              {ω | ¬ |boolZ ω -
                    (∫ ω, boolZ ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))| ≤ t} ≤
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp)))))) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun a Omega =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff a i j)
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
        let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |process a Omega|)
        bernoulliEventProb p
            (fun Omega => ¬ |Z Omega - bernoulliExpectation p Z| ≤ t) ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  sorry
