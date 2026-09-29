-- Prove2me | Theorems.Thm_MeasureTheory_uniformIntegrable_one_of_sq_bounded_approx
-- name    : MeasureTheory.uniformIntegrable_one_of_sq_bounded_approx
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T10:53:19.747858+00:00
-- url     : https://prove2.me/theorems/855dfcb2-3249-4ca1-8227-7dd8227b536f
-- title:
--   Uniform integrability from an $L^2$-bounded approximation
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $(f_n)_{n\ge0}$ be measurable, nonnegative and integrable with $\int f_n\,dP\le 1$ for every $n$.
--
--   Suppose that for every $\varepsilon>0$ the family can be split, from some index $N$ on, into a part bounded in $L^2$ and a part small in $L^1$: there are $N$, nonnegative measurable families $(u_n)$, $(w_n)$ and a constant $M$ with $u_n\in L^2(P)$, $w_n\in L^1(P)$,
--
--   $$f_n\le u_n+w_n,\qquad \int u_n^2\,dP\le M,\qquad \int w_n\,dP\le\varepsilon\qquad (n\ge N).$$
--
--   Then $(f_n)$ is uniformly integrable in $L^1(P)$.
--
--   This is the mechanism behind uniform-integrability proofs for normalized partial sums of dependent sequences: one truncates the summands, controls the truncated sums through a fourth-moment inequality (which gives the $L^2$ bound on $u_n=2A_n^2/\sigma_n^2$), and controls the discarded tail in $L^1$. The proof is the two-sided estimate
--
--   $$\int_{\{f_n\ge C\}} f_n\,dP\ \le\ \Bigl(\int u_n^2\,dP\Bigr)^{1/2}P(f_n\ge C)^{1/2}+\int w_n\,dP\ \le\ \sqrt{M/C}+\varepsilon,$$
--
--   by Cauchy–Schwarz and Markov's inequality, together with the fact that each of the finitely many remaining members is integrable, so that its own tail integral is small for a large enough threshold.
-- source:
--   Standard uniform-integrability criterion (Cauchy--Schwarz plus Markov, in the tail formulation of MeasureTheory.uniformIntegrable_of). It is the abstract form of the argument used for the uniform integrability of S_n^2/sigma_n^2 in P. Doukhan, P. Massart and E. Rio, The functional central limit theorem for strongly mixing processes, Ann. Inst. H. Poincare Probab. Statist. 30 (1994) 63-82, Theorem 1, as cited in G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, Theorem 6.

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem MeasureTheory.uniformIntegrable_one_of_sq_bounded_approx {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hfm : ∀ n, Measurable (f n)) (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfint : ∀ n, Integrable (f n) P) (hfle : ∀ n, ∫ ω, f n ω ∂P ≤ 1)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ u w : ℕ → Ω → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, N ≤ n → MemLp (u n) 2 P) ∧ (∀ n, N ≤ n → Integrable (w n) P) ∧
      (∀ n, N ≤ n → ∀ ω, 0 ≤ u n ω) ∧ (∀ n, N ≤ n → ∀ ω, 0 ≤ w n ω) ∧
      (∀ n, N ≤ n → ∀ ω, f n ω ≤ u n ω + w n ω) ∧
      (∀ n, N ≤ n → ∫ ω, (u n ω) ^ 2 ∂P ≤ M) ∧
      (∀ n, N ≤ n → ∫ ω, w n ω ∂P ≤ ε)) :
    UniformIntegrable f 1 P := by sorry
