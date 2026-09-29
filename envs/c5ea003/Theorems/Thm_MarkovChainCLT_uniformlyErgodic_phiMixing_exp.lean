-- Prove2me | Theorems.Thm_MarkovChainCLT_uniformlyErgodic_phiMixing_exp
-- name    : MarkovChainCLT.uniformlyErgodic_phiMixing_exp
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:17:02.153287+00:00
-- url     : https://prove2.me/theorems/d67f40c9-1e39-4381-ad9f-030041a26059
-- title:
--   Uniform ergodicity gives exponentially fast $\varphi$-mixing
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with invariant distribution $\pi$. If $X$ is **uniformly ergodic**, i.e. $\|P^n(x,\cdot) - \pi\| \le R\,t^n$ for a constant $R$ not depending on the starting point and some $t < 1$, then the stationary chain is uniformly ($\varphi$-) mixing at an exponential rate: there are $c \ge 0$ and $\theta > 0$ with
--
--   $$\varphi(n) \le c\,e^{-\theta n} \qquad (n \ge 1),$$
--
--   that is, $\varphi(n) = O(e^{-\theta n})$.
--
--   A Harris ergodic chain is uniformly ergodic if and only if it is uniformly mixing (Ibragimov & Linnik 1971, pp. 367-368), and as a consequence of the strong Markov property a $\varphi$-mixing Harris ergodic chain automatically enjoys exponentially fast $\varphi$-mixing (Bradley 1986, Theorem 4.2).
--
--   This is the quantitative half of the mission's Theorem 2(iv), stated for a general measurable state space. It is the form in which uniform ergodicity is consumed by Corollary 5: exponential decay of $\varphi$ makes Billingsley's summability condition $\sum_n \sqrt{\varphi(n)} < \infty$ (eq. (13)) immediate, which is exactly the source's remark that "if $X$ is uniformly ergodic the coefficients $\varphi(n)$ decrease exponentially and (13) is obvious".
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 3 (Theorem 2, part 4, arXiv v2 p. 8) and the remark preceding Corollary 5 (arXiv v2 p. 12); original sources Ibragimov & Linnik (1971), pp. 367-368, and Bradley (1986), Theorem 4.2.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.uniformlyErgodic_phiMixing_exp {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π) :
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
      phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n ≤ c * Real.exp (-θ * n) := by sorry
