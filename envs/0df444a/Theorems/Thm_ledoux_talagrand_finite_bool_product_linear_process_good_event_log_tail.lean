-- Prove2me | Theorems.Thm_ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail
-- name    : ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T03:59:34.632484+00:00
-- url     : https://prove2.me/theorems/f80afd3f-9738-43f7-abf4-d15e4856d014
-- statement:
--   Generic finite Boolean product-measure Ledoux--Talagrand concentration theorem in good-event form.
--
--   Primary source: Ledoux, *The Concentration of Measure Phenomenon*, Section 7, Corollary 7.8. Mission source connection: Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9), states the equivalent bad-event form, and Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2), cites this Talagrand--Ledoux product-space concentration input for the matrix-completion tangent-sampling proof.
--
--   Mathematical statement and notation: let $\kappa$ be a finite coordinate type and let $\omega:\kappa\to\{0,1\}$ be sampled from the independent product Bernoulli probability model
--   $$
--   \mu_p=\prod_{x\in\kappa}\mathrm{Bernoulli}(p),\qquad 0\le p\le1,
--   $$
--   represented in Lean as `p : NNReal` with proof `hp : p \le 1`. For a finite nonempty coefficient class $c_a(x)$ indexed by $a\in\iota$, define
--   $$
--   S_a(\omega)=\sum_{x\in\kappa}(\omega_x-p)c_a(x),\qquad
--   Z(\omega)=\max_a S_a(\omega),\qquad
--   \bar Z(\omega)=\max_a |S_a(\omega)|.
--   $$
--   Assume the envelope bound
--   $$
--   |c_a(x)|\le B
--   $$
--   for all $a,x$, with $B>0$, and the variance proxy bound
--   $$
--   \sum_{x\in\kappa}p(1-p)c_a(x)^2\le\sigma^2
--   $$
--   for every $a$. Then there is a universal constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_{\mu_p}\{|Z-\mathbb E_{\mu_p}Z|\le t\}
--   \ge
--   1-3\exp\!\left(-{t\over KB}\log\left(1+{Bt\over\sigma^2+B\mathbb E_{\mu_p}\bar Z}\right)\right).
--   $$
--   Here $\kappa,p,B,\sigma^2,t,Z,\bar Z$ and the product Bernoulli probability model are the main quantities. The matrix dimensions $n_1,n_2$, powerset sample set $\Omega$, fixed-cardinality `successProb`, and coherence parameters $\mu_0,\mu_1$ do not appear in this external concentration theorem; they appear only after specializing $\kappa=[n_1]\times[n_2]$ in downstream matrix-completion nodes.
--
--   Formalization note: this is a direct source theorem / source-derived finite Boolean product-measure formulation of the Ledoux--Talagrand concentration input. It is not a formal bridge and not a Lean-only arithmetic lemma. The parent `candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail` is a formal complement bridge from this good-event theorem to the Candes--Romberg bad-event theorem.
-- source:
--   Ledoux, *The Concentration of Measure Phenomenon*, Section 7, Corollary 7.8; Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9); cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → κ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ x : κ, |coeff a x| ≤ B) →
        (∀ a : ι,
          ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * (coeff a x) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → (κ → Bool) → ℝ :=
          fun a ω =>
            ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
        let boolZ : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)).real
            {ω | |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω
                        ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure))))))
        := by
  sorry
