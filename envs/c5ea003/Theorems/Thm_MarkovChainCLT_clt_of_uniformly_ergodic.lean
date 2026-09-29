-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_uniformly_ergodic
-- name    : MarkovChainCLT.clt_of_uniformly_ergodic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:42:35.122209+00:00
-- url     : https://prove2.me/theorems/3e0290c5-2168-4037-b905-021f131a7714
-- title:
--   Uniformly ergodic CLT: $E_\pi f^2 < \infty$ (Jones Cor 5)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose the chain is uniformly ergodic and
--
--   $$
--   E_\pi f^2 < \infty.
--   $$
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   The Tierney/Ibragimov–Linnik CLT for uniformly ergodic chains: under the strongest ergodicity condition, a second moment on the functional is all that is needed.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Corollary 5 (arXiv v2 p. 13; proved there from Theorem 8 via Theorem 2(iv)); originals: Ibragimov & Linnik (1971); L. Tierney, Markov chains for exploring posterior distributions, Ann. Statist. 22 (1994)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 5** (Ibragimov–Linnik 1971; Tierney 1994): a uniformly ergodic
Harris chain with `E_π f² < ∞` satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_uniformly_ergodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (huni : UniformlyErgodic P π) (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by sorry
