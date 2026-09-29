-- Prove2me | Theorems.Thm_MarkovChainCLT_phiMixingCoef_le_exp_of_uniformlyErgodic
-- name    : MarkovChainCLT.phiMixingCoef_le_exp_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:22:35.9716+00:00
-- url     : https://prove2.me/theorems/2120a239-cfd1-4030-bf9e-fc4349c14f20
-- title:
--   Uniform ergodicity gives exponentially fast $\varphi$-mixing (forward half of Jones Thm 2(iv))
-- statement:
--   Let $P$ be a Markov kernel with invariant probability $\pi$. If the chain is **uniformly ergodic** — there are constants $R \ge 0$ and $t \in [0,1)$ with $\|P^n(x,\cdot) - \pi\| \le R\,t^n$ for all $x$ and all $n \ge 1$ — then its stationary version is **uniformly ($\varphi$-) mixing at an exponential rate**: there exist $c \ge 0$ and $\theta > 0$ such that
--
--   $$\varphi(n) \;\le\; c\,e^{-\theta n} \qquad (n \ge 1).$$
--
--   **What it establishes.** This is the forward implication of the Ibragimov–Linnik equivalence between the strongest classical ergodicity condition and the strongest classical mixing condition, together with the quantitative rate. It is the direction that feeds the applications: the $\varphi$-mixing central limit theorem of Billingsley requires $\sum_n \sqrt{\varphi(n)} < \infty$, and an exponential rate makes that series converge with room to spare — which is why the uniformly ergodic CLT (Tierney) needs no moment condition beyond square integrability.
--
--   **Where the content sits.** All of the probabilistic work is in the bound $\varphi(n) \le \sup_x \|P^n(x,\cdot) - \pi\|$, which requires disintegrating a "past $\cap$ future" probability over the past, identifying the conditional law of the future as a chain restarted from $P^n(u_k,\cdot)$, and bounding an average of $[0,1]$-valued integrals by a total-variation distance — all uniformly in the split point $k$. Given that bound, the present statement is the observation that a geometric rate is an exponential rate.
--
--   **The one subtlety.** Writing $t^n$ as $e^{-\theta n}$ requires $\theta = -\log t$, which is undefined at $t = 0$ — and $t = 0$ is permitted by the definition of uniform ergodicity (it describes a chain that reaches stationarity exactly after one step). The fix is to replace $t$ by $t' = \max(t, 1/2)$: still strictly less than $1$, now bounded away from $0$, and $t^n \le t'^n$ since $t \le t'$. Then $\theta = -\log t' > 0$ works uniformly, at the cost of a rate that is no worse than the true one.
--
--   **Proof.** Unpack uniform ergodicity to get $R, t$. Set $t' = \max(t,1/2)$ and $\theta = -\log t'$, so $\theta > 0$ because $0 < t' < 1$, and $e^{-\theta n} = (e^{\log t'})^n = t'^n$. For each $n \ge 1$ and each $x$, $\|P^n(x,\cdot) - \pi\| \le R t^n \le R t'^n = R e^{-\theta n}$. Applying the bound of $\varphi(n)$ by a uniform total-variation rate with $C = R e^{-\theta n}$ gives the claim with $c = R$.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971, pp. 367-368; R. C. Bradley, "Basic Properties of Strong Mixing Conditions", Probability Surveys 2 (2005) 107-144; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Theorem 2(iv).

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem MarkovChainCLT.phiMixingCoef_le_exp_of_uniformlyErgodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π) :
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
      phiMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n
        ≤ c * Real.exp (-θ * n) := by sorry
