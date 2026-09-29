-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_iff_boundedInProbability
-- name    : MarkovChainCLT.clt_iff_boundedInProbability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-15T14:39:14.396799+00:00
-- url     : https://prove2.me/theorems/d6ae81a7-25bd-4318-94c3-0217a5280537
-- title:
--   Chen characterization: CLT $\iff$ $\sqrt{n}\bar f_n$ bounded in probability (Jones Thm 4)
-- statement:
--   Let $X$ be a Markov chain with transition kernel $P$, Harris ergodic with invariant probability $\pi$, and let $f$ be measurable with $E_\pi f = 0$ and $E_\pi f^2 < \infty$. Then, for the stationary chain (initial distribution $\pi$), the following are equivalent:
--
--   $$
--   \sqrt{n}\, \bar f_n \xrightarrow{d} N(0, \sigma^2) \;\text{ for some } \sigma^2 \ge 0 \qquad \Longleftrightarrow \qquad \bigl(\sqrt{n}\, \bar f_n\bigr)_{n \ge 1} \text{ is bounded in probability.}
--   $$
--
--   Chen's characterization shows the Markov chain CLT is equivalent to mere tightness of the normalized averages — the sharpest available dividing line for square-integrable functionals. By the source's Remark 2, the CLT side is then automatic for every initial distribution.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat. The $\sigma$-algebra of the state space is additionally assumed countably generated, the standard general-state-space setting of Meyn and Tweedie.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 4 (arXiv v2 p. 9); original: X. Chen, Limit theorems for functionals of ergodic Markov chains with general state space, Mem. Amer. Math. Soc. 139 (1999)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 4** (Chen 1999): for a Harris ergodic chain and a centered
square-integrable functional, the stationary chain satisfies a CLT
`√n f̄_n →d N(0, σ²)` for some `σ² ≥ 0` **iff** the sequence `√n f̄_n` is bounded
in probability. -/

theorem MarkovChainCLT.clt_iff_boundedInProbability {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcent : ∫ x, f x ∂π = 0) (hL2 : MemLp f 2 π) :
    (∃ v : ℝ≥0, TendstoInDistribution
        (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
        atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v))
      ↔ BoundedInProbability
          (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
          (chainMeasure P π) := by sorry
