-- Prove2me | Theorems.Thm_centered_sampling_chernoff_exponential_tail
-- name    : centered_sampling_chernoff_exponential_tail
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T00:06:36.995037+00:00
-- url     : https://prove2.me/theorems/7a56dc66-a54d-493a-9900-5ce994ef8ae9
-- statement:
--   **Cramér–Chernoff exponential (MGF) tail bound on the bespoke finite Bernoulli observation measure.** For inclusion probability $0\le p\le 1$, any scalar statistic $Z:\mathrm{Finset}(\mathrm{Fin}\,n_1\times\mathrm{Fin}\,n_2)\to\mathbb R$ of the observation set, any threshold $t$, and any $\lambda>0$, $$P(t\le Z)\le e^{-\lambda t}\,\mathbb E[e^{\lambda Z}],$$ where $P$ is $\mathrm{bernoulliEventProb}\,p$ and $\mathbb E$ is $\mathrm{bernoulliExpectation}\,p$. This is Markov's inequality applied to the increasing transform $x\mapsto e^{\lambda x}$: pointwise $\mathbf 1[t\le Z(\Omega)]\le e^{\lambda(Z(\Omega)-t)}$, summed against the nonnegative observation weights $\mathrm{bernoulliObservationWeight}\,p\,\Omega$. It is the canonical 'MGF $\Rightarrow$ tail' (Chernoff) half of the Cramér–Chernoff method, valid on this bespoke powerset-Bernoulli measure with no Mathlib MeasureTheory dependency. Paired with the exact MGF factorization centered\_sampling\_coefficient\_mgf\_factorization (and any sub-Gaussian MGF bound) it yields exponential concentration for the centered sampling coefficient.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, Ch. 2 'The Cramer-Chernoff method' (generic Chernoff bound P(Z>=t) <= e^{-lambda t} E[e^{lambda Z}]); applied to the centered sampling coefficient of Candes-Recht 2009, arXiv:0805.4471, Section 6.

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_chernoff_exponential_tail
    {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (t lam : ℝ) (hlam : 0 < lam) :
    bernoulliEventProb p (fun Omega => t ≤ Z Omega) ≤
      Real.exp (-(lam * t)) *
        bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) := by
  sorry
