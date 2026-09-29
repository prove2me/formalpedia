-- Prove2me | Theorems.Thm_candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail
-- name    : candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T03:27:57.472295+00:00
-- url     : https://prove2.me/theorems/a6a54193-a0d6-4ca1-9609-5785edcaebdf
-- statement:
--   Finite Boolean product-measure Candes--Romberg Talagrand bad-event theorem for a finite coordinate set.
--
--   Primary source: Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9). Mission source connection: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2), cites the same Talagrand--Ledoux empirical-process input for the tangent-sampling proof.
--
--   Mathematical statement and notation: let $\kappa$ be a finite coordinate type and let $\omega:\kappa\to\{0,1\}$ be sampled from the independent product Bernoulli measure
--   $$
--   \mu_p=\prod_{x\in\kappa}\mathrm{Bernoulli}(p),\qquad 0\le p\le 1,
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
--   \sum_{x\in\kappa}p(1-p)c_a(x)^2\le \sigma^2
--   $$
--   for every $a$. Then there is a universal constant $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_{\mu_p}\{|Z-\mathbb E_{\mu_p}Z|>t\}
--   \le
--   3\exp\!\left(-{t\over KB}\log\left(1+{Bt\over\sigma^2+B\mathbb E_{\mu_p}\bar Z}\right)\right).
--   $$
--   Here $\kappa,p,B,\sigma^2,t,Z,\bar Z$ and the product Bernoulli probability model are the main quantities. The matrix dimensions $n_1,n_2$, powerset sample set $\Omega$, fixed-cardinality `successProb`, and coherence parameters $\mu_0,\mu_1$ do not appear in this external concentration theorem; they appear only after specializing $\kappa=[n_1]\times[n_2]$ in downstream matrix-completion nodes.
--
--   Formalization note: this is a direct source theorem / source-derived finite Boolean product-measure formulation of Candes--Romberg Theorem 3.2, not a formal bridge and not a Lean-only arithmetic lemma. The child theorem `candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail` is the formal specialization to $\kappa=\mathrm{Fin}\,n_1\times\mathrm{Fin}\,n_2$ with `bernMeasure` unfolded to Mathlib's product measure.
-- source:
--   Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2, equation (3.9); cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail :
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
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω
                      ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure))))))
        := by
  sorry
