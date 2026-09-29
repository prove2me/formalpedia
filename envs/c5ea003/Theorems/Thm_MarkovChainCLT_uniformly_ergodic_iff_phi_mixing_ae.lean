-- Prove2me | Theorems.Thm_MarkovChainCLT_uniformly_ergodic_iff_phi_mixing_ae
-- name    : MarkovChainCLT.uniformly_ergodic_iff_phi_mixing_ae
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T04:14:16.55655+00:00
-- url     : https://prove2.me/theorems/bc5324cf-8b31-42f6-b220-9e7d5454e515
-- title:
--   Theorem 2(iv), corrected: uniform ergodicity vs. $\varphi$-mixing (Doeblin's full-measure form)
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with transition kernel $P$ and stationary distribution $\pi$ on a countably generated state space. Then:
--
--   1. **(uniform ergodicity $\Rightarrow$ uniform mixing)** If $X$ is uniformly ergodic then $\varphi(n) \to 0$.
--   2. **(uniform mixing $\Rightarrow$ uniform ergodicity, $\pi$-a.e.)** If $\varphi(n) \to 0$ then there exist $R \ge 0$ and $t \in [0, 1)$ such that for $\pi$-almost every $x$ and every $n \ge 1$, $\|P^n(x, \cdot) - \pi\| \le R\,t^n$.
--   3. **(exponential rate)** If $X$ is uniformly ergodic then there exist $c \ge 0$ and $\theta > 0$ with $\varphi(n) \le c\,e^{-\theta n}$ for all $n \ge 1$.
--
--   This is the corrected form of Theorem 2(iv) of Jones (2004). Jones states the equivalence with uniform ergodicity in the sense of his eq. (3) — $\|P^n(x,\cdot) - \pi\| \le M(x)t^n$ with $M$ bounded, at **every** $x$ — but that reading of the converse is false: the countdown chain $P(x,\cdot) = \delta_{x-1}$ on $\mathbb{N}$ with $\pi = \delta_0$ is Harris ergodic and has $\varphi(n) \equiv 0$ (its stationary version is the constant-zero path), yet $\sup_x \|P^n(x,\cdot) - \pi\| = 1$ for every $n$. The obstruction is structural: the mixing coefficients depend only on the law of the stationary process and so constrain $P$ only on $\operatorname{supp}\pi$. Doeblin's theorem, as stated verbatim in Bradley's survey §3.2, restricts both hypothesis and conclusion to a set $A$ with $\mu(A) = 1$; part 2 above is that full-measure form. Part 1 is the direction Jones actually uses downstream and is already proved instance-free as `MarkovChainCLT.uniformlyErgodic_phiMixing_exp`.
-- source:
--   Galin L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 2, part 4 (p. 8) and eq. (3) (p. 3) — corrected to the full-measure-set form of the primary source: W. Doeblin (1938), as stated verbatim in R.C. Bradley, Basic Properties of Strong Mixing Conditions: A Survey and Some Open Questions, Probability Surveys 2 (2005) 107-144, https://arxiv.org/abs/math/0511078, section 3.2 and Theorem 3.4(2); Ibragimov & Linnik 1971, pp. 367-368; Bradley 1986, Theorem 4.2

import Definitions.Def_MixingCoefficients
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.uniformly_ergodic_iff_phi_mixing_ae {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π) :
    (MarkovChainCLT.UniformlyErgodic P π →
        Tendsto (fun n => MarkovChainCLT.phiMixingCoef
          (MarkovChainCLT.chainMeasure P π) (fun i ω => ω i) n) atTop (𝓝 0))
    ∧ (Tendsto (fun n => MarkovChainCLT.phiMixingCoef
          (MarkovChainCLT.chainMeasure P π) (fun i ω => ω i) n) atTop (𝓝 0) →
        ∃ R t : ℝ, 0 ≤ R ∧ 0 ≤ t ∧ t < 1 ∧
          ∀ᵐ x ∂π, ∀ n : ℕ, 1 ≤ n →
            MarkovChainCLT.tvDist (MarkovChainCLT.iterKernel P n x) π ≤ R * t ^ n)
    ∧ (MarkovChainCLT.UniformlyErgodic P π → ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
        MarkovChainCLT.phiMixingCoef (MarkovChainCLT.chainMeasure P π)
          (fun i ω => ω i) n ≤ c * Real.exp (-θ * n)) := by sorry
