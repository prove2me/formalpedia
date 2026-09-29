-- Prove2me | Theorems.Thm_MarkovChainCLT_rho_mixing_exp_of_geometric_reversible
-- name    : MarkovChainCLT.rho_mixing_exp_of_geometric_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:38:19.280728+00:00
-- url     : https://prove2.me/theorems/34bb8995-3100-46f5-bb85-e3a403311bc2
-- title:
--   Geometric ergodicity + detailed balance $\Rightarrow$ exponential $\rho$-mixing (Jones Thm 2(iii))
-- statement:
--   Let $X$ be a Markov chain with transition kernel $P$, Harris ergodic with invariant probability $\pi$. Suppose the chain is geometrically ergodic and reversible with respect to $\pi$ (detailed balance, the source's eq. (8)). Then the stationary chain is asymptotically uncorrelated with exponentially fast $\rho$-mixing: there exist $c \ge 0$ and $\theta > 0$ such that
--
--   $$
--   \rho(n) \;\le\; c\, e^{-\theta n} \qquad (n \ge 1).
--   $$
--
--   Reversibility holds by construction for Metropolis–Hastings samplers, so this result (Roberts–Rosenthal 1997) is the gateway to second-moment CLTs for the most common MCMC algorithms.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 2, part 3 (arXiv v2 p. 8; detailed balance = eq. (8)); original: G. O. Roberts & J. S. Rosenthal, Geometric ergodicity and hybrid Markov chains, Electron. Comm. Probab. 2 (1997), Theorem 2.1, plus R. C. Bradley (1986), Theorem 4.2

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 2, part 3** (Roberts–Rosenthal 1997): a geometrically ergodic chain
satisfying detailed balance is asymptotically uncorrelated, with exponentially fast
ρ-mixing. -/

theorem MarkovChainCLT.rho_mixing_exp_of_geometric_reversible {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π)
    (hrev : Kernel.IsReversible P π) :
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
      rhoMixingCoef (chainMeasure P π) (fun i ω => ω i) n ≤ c * Real.exp (-θ * n) := by sorry
