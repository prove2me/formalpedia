-- Prove2me | Theorems.Thm_MarkovChainCLT_tendsto_nat_mul_alphaMixingCoef_of_summable
-- name    : MarkovChainCLT.tendsto_nat_mul_alphaMixingCoef_of_summable
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T12:20:58.60536+00:00
-- url     : https://prove2.me/theorems/6268b9ea-fa4d-4654-9669-2dc1345ac5ca
-- title:
--   Summable $\alpha$-mixing coefficients satisfy $n\,\alpha(n)\to0$
-- statement:
--   **Summable strong mixing coefficients decay faster than $1/n$.**
--
--   Let $Y$ be a sequence of random elements on a probability space with strong mixing coefficients $\alpha(n)$, and suppose $\sum_{n\ge0}\alpha(n)<\infty$.  Then
--
--   $$n\,\alpha(n)\longrightarrow 0\qquad (n\to\infty).$$
--
--   This is more than the vanishing of the terms of a convergent series: it uses that the coefficients $\alpha(n)$ are nonnegative and *nonincreasing* in $n$.  For such a sequence the classical Abel–Pringsheim argument applies: for $k$ between $\lfloor n/2\rfloor$ and $n-1$ one has $\alpha(n)\le\alpha(k)$, so
--
--   $$\tfrac n2\,\alpha(n)\;\le\;\bigl(n-\lfloor n/2\rfloor\bigr)\alpha(n)\;\le\!\!\sum_{k=\lfloor n/2\rfloor}^{n-1}\!\!\alpha(k)\;\le\;\sum_{k\ge \lfloor n/2\rfloor}\alpha(k),$$
--
--   and the right-hand tail of a convergent series tends to $0$ as $\lfloor n/2\rfloor\to\infty$.
--
--   The statement is the quantitative form in which the hypothesis $\sum_n\alpha(n)<\infty$ of the Ibragimov bounded-case central limit theorem is actually used.  In Bernstein's big-block/small-block decomposition of $S_n$ one takes $k$ blocks of length $p$ separated by gaps of length $q$; the blocks decouple up to an error $16\,k\,\alpha(q)$, and with $k$ and $q$ both of order $\sqrt n$ this error is a bounded multiple of $q\,\alpha(q)$, which vanishes precisely by the display above.  Summability of $\alpha$ alone, without monotonicity, would not give this.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5 condition 1 (the hypothesis is the summability of the strong mixing coefficients of a bounded stationary sequence); the elementary fact that a nonincreasing nonnegative summable sequence satisfies n a_n -> 0 is classical (Abel; Pringsheim), see K. Knopp, "Theory and Application of Infinite Series", Section 82. Monotonicity of the mixing coefficients is Section 1 of R. C. Bradley, "Basic Properties of Strong Mixing Conditions", Probability Surveys 2 (2005).

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.tendsto_nat_mul_alphaMixingCoef_of_summable {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hα : Summable fun n => alphaMixingCoef P Y n) :
    Tendsto (fun n : ℕ => (n : ℝ) * alphaMixingCoef P Y n) atTop (𝓝 0) := by sorry
