-- Prove2me | Theorems.Thm_MarkovChainCLT_boundedInProbability_of_tendstoInDistribution
-- name    : MarkovChainCLT.boundedInProbability_of_tendstoInDistribution
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T06:54:55.488889+00:00
-- url     : https://prove2.me/theorems/63e63d5e-4373-4742-aad1-e78ceb619ec4
-- title:
--   Convergence in distribution implies boundedness in probability
-- statement:
--   Let $(Z_n)_{n\ge 0}$ be real-valued random variables on a probability space $(\Omega,\mathcal F,P)$, and suppose that $Z_n$ converges in distribution to a real random variable $W$ defined on some probability space $(\Omega',\mathcal F',P')$. Then the sequence $(Z_n)$ is **bounded in probability** (tight): for every $\varepsilon>0$ there is a constant $K$ with
--
--   $$\sup_{n\ge 0} P\bigl(|Z_n| > K\bigr) \le \varepsilon .$$
--
--   This is the elementary half of the relation between weak convergence and tightness on the real line: a weakly convergent sequence of laws is automatically tight. It is what turns the "CLT" side of Chen's characterization (Jones 2004, Theorem 4) into the "bounded in probability" side.
--
--   The proof uses only the portmanteau inequality for closed sets. Given $\varepsilon>0$, choose $K_0$ so that the limit law puts mass at most $\varepsilon/2$ on the closed set $F=\{x: |x|\ge K_0\}$, which is possible because $\bigcap_{k\in\mathbb N}\{x : |x|>k\}=\emptyset$ and the limit law is finite. Portmanteau gives $\limsup_n P(Z_n\in F)\le \varepsilon/2<\varepsilon$, so $P(|Z_n|>K_0)\le\varepsilon$ for all large $n$; each of the remaining finitely many laws is itself a probability measure and so has its own small tail, and the maximum of the resulting thresholds works uniformly.
--
--   **Formalization Note** Convergence in distribution is weak convergence of the laws, allowing the limit variable to live on a different probability space; boundedness in probability is the platform's `BoundedInProbability` predicate, phrased with the real number $P(\{|Z_n|>K\})$.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley (1999), Theorem 2.1 (portmanteau) and Section 5 (tightness of weakly convergent sequences on a Polish space); used as the elementary direction of G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 4 (arXiv v2 p. 9).

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- A sequence of real random variables that converges in distribution is bounded in
probability. -/
theorem MarkovChainCLT.boundedInProbability_of_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℕ → Ω → ℝ) (W : Ω' → ℝ)
    (h : TendstoInDistribution Z atTop W (fun _ => P) P') :
    MarkovChainCLT.BoundedInProbability Z P := by sorry
