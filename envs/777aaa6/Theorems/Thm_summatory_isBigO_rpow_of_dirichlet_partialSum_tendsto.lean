-- Prove2me | Theorems.Thm_summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
-- name    : summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T19:51:35.732261+00:00
-- url     : https://prove2.me/theorems/72bac3e2-8372-42c8-b774-b2c1c9820eef
-- title:
--   Abel summation: convergence of $\sum a_n n^{-\sigma}$ gives $\sum_{n\le N}a_n=O(N^{\sigma})$
-- statement:
--   Let $a:\mathbb N\to\mathbb C$ be any sequence, let $\sigma>0$, and suppose the weighted partial sums
--
--   $$S_N=\sum_{n=1}^{N}\frac{a_n}{n^{\sigma}}$$
--
--   converge to a limit $L$ as $N\to\infty$. Then the unweighted partial sums satisfy
--
--   $$A_N=\sum_{n=1}^{N}a_n=O\!\left(N^{\sigma}\right)\qquad(N\to\infty).$$
--
--   This is the elementary partial-summation step that converts convergence of a Dirichlet series at a real abscissa $\sigma>0$ into a growth bound of order $\sigma$ for the summatory function of its coefficients. It is the standard device by which the convergence form of a Dirichlet-series hypothesis is transferred to the coefficient sums, for instance in the equivalences of Titchmarsh and Heath-Brown, Section 14.25.
--
--   The proof is Abel summation together with a telescoping estimate: writing $a_n=n^{\sigma}(S_n-S_{n-1})$ one obtains
--
--   $$A_N=N^{\sigma}S_N-\sum_{n=1}^{N-1}\bigl((n+1)^{\sigma}-n^{\sigma}\bigr)S_n,$$
--
--   and if $|S_n|\le M$ for all $n$, which holds because $(S_n)$ converges, then
--
--   $$|A_N|\le MN^{\sigma}+M\sum_{n=1}^{N-1}\bigl((n+1)^{\sigma}-n^{\sigma}\bigr)=MN^{\sigma}+M\bigl(N^{\sigma}-1\bigr)\le 2MN^{\sigma}.$$
--
--   Only boundedness of $(S_N)$ is used; convergence is assumed because that is the form in which the hypothesis usually arises.
--
--   **Formalization Note.** Sums run over `Finset.Icc 1 N`, the weight is the real power `(n : ℝ) ^ (-σ)` coerced into $\mathbb C$, and the conclusion is Lean's `IsBigO` along `atTop` against $N\mapsto N^{\sigma}$.
-- source:
--   Standard partial-summation lemma; used in this form in E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, Section 14.25, p. 370, in passing between the series form 14.25(A) and the summatory form 14.25(C).

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
    (a : ℕ → ℂ) (σ : ℝ) (hσ : 0 < σ) (L : ℂ)
    (h : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * ((n : ℝ) ^ (-σ) : ℝ))
      Filter.atTop (nhds L)) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      (fun N : ℕ => (N : ℝ) ^ σ) := by sorry
