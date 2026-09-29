-- Prove2me | Theorems.Thm_candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
-- name    : candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T02:46:46.063279+00:00
-- url     : https://prove2.me/theorems/e2da553c-8c2d-4e87-a880-d3e9ee79eb75
-- statement:
--   Boolean product-measure version of the finite Bernoulli-coordinate Candes--Romberg Talagrand bad-event theorem.
--
--   Primary source: Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9). Mission source connection: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2), cites this Talagrand--Ledoux empirical-process input for the matrix-completion tangent sampling proof.
--
--   Mathematical statement and notation: let $\omega:[n_1]\times[n_2]\to\{0,1\}$ be sampled from the independent product Bernoulli measure $\mathrm{bernMeasure}(p)$, where $p\in[0,1]$ is represented in Lean as `p : NNReal` with proof `hp : p \le 1`. For a finite nonempty coefficient class $c_a(i,j)$ indexed by $a\in\iota$, define
--   $$
--   S_a(\omega)=\sum_{i,j}(\omega_{ij}-p)c_a(i,j),\qquad
--   Z(\omega)=\max_a S_a(\omega),\qquad
--   \bar Z(\omega)=\max_a |S_a(\omega)|.
--   $$
--   Assume the envelope bound
--   $$
--   |c_a(i,j)|\le B
--   $$
--   for all $a,i,j$, with $B>0$, and the variance proxy bound
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le\sigma^2
--   $$
--   for every $a$. Then there is a universal constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_{\mathrm{bernMeasure}(p)}\{|Z-\mathbb E Z|>t\}
--   \le
--   3\exp\!\left(-{t\over KB}\log\left(1+{Bt\over\sigma^2+B\mathbb E\bar Z}\right)\right).
--   $$
--   Here $n_1,n_2,p,B,\sigma^2,t,Z,\bar Z$ are the main quantities. The powerset sample set $\Omega$, the fixed-cardinality success probability `successProb`, and the coherence parameters $\mu_0,\mu_1$ do not appear in this external concentration leaf.
--
--   Formalization note: this is a direct source theorem / source-derived finite Boolean product-measure formulation of Candes--Romberg Theorem 3.2, not a formal bridge and not a Lean-only arithmetic lemma. It is intended as the source-backed analytic child used by the formal bridge `candes_romberg_bad_event_powerset_from_bool_product_coordinate_process`, which transfers the result to the powerset `bernoulliEventProb` theorem `candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail`.
-- source:
--   Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9); cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail :
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
                    (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))))) := by
  sorry
