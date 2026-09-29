-- Prove2me | Theorems.Thm_MarkovChainCLT_tvDist_chainMeasure_shift_le
-- name    : MarkovChainCLT.tvDist_chainMeasure_shift_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:05:24.046092+00:00
-- url     : https://prove2.me/theorems/6ee6b1c0-02aa-4781-872d-1c46cc9e5b02
-- title:
--   After a burn-in of $m$ steps, any initial distribution is within $C$ of stationarity on path space
-- statement:
--   Let $P$ be a Markov kernel with invariant probability $\pi$, let $\lambda$ be an arbitrary initial distribution, and suppose the $m$-step kernel satisfies the uniform bound $\|P^m(x,\cdot)-\pi\| \le C$ for every $x$. Then, on **path space**,
--
--   $$\Bigl\|\bigl(\sigma^{m}\bigr)_{*}\mathbb P_\lambda \;-\; \mathbb P_\pi\Bigr\| \;\le\; C,$$
--
--   where $\sigma^m$ is the shift $(\sigma^m\omega)_n = \omega_{n+m}$.
--
--   **What it says.** *A chain started from an arbitrary distribution, observed from time $m$ onwards, is within $C$ of the stationary chain — not merely at time $m$, but as an entire trajectory.* This is the precise sense in which a chain "forgets its initial distribution", and it is the form the statement must take to be useful for limit theorems, which are statements about the whole path rather than about a single marginal.
--
--   **Why it is the bridge in the Markov chain CLT.** The central limit theorem asserts convergence *for every initial distribution*, while every proof of it establishes the limit for the *stationary* chain. For a uniformly ergodic chain, $C = R\,t^m$ decays geometrically, so this bound says the two path laws are geometrically close after a burn-in of $m$ steps. Since the normalized partial sums $\sqrt n(\bar f_n - \mathbb E_\pi f)$ are asymptotically unaffected by discarding a fixed number of initial terms, testing against a bounded continuous $g$ gives
--   $$\bigl|\mathbb E_\lambda[g(T_n\circ\sigma^m)] - \mathbb E_\pi[g(T_n)]\bigr| \;\le\; 2\|g\|_\infty\,R\,t^m ,$$
--   and letting $n \to \infty$ and then $m \to \infty$ transfers the stationary limit law to $\lambda$.
--
--   **Two distinct total-variation facts combine here**, and neither alone suffices. First, a bound holding from every *deterministic* start transfers to any *random* start with the same constant, giving $\|\lambda P^m - \pi\| \le C$. Second, applying the trajectory kernel to both sides cannot increase total variation, lifting that state-space bound to path space. The first preserves the constant; the second is a contraction. Their composition is what turns a hypothesis about the $m$-step kernel into a statement about entire trajectories.
--
--   **Proof.** Shifting a trajectory by $m$ steps is the same as taking $m$ steps of $P$ first and then running the chain, so $(\sigma^m)_*\mathbb P_\lambda = \mathbb P_{\lambda P^m}$ — formally, the trajectory kernel composed with $P^m \circ \lambda$. Data processing bounds the distance between $\mathbb P_{\lambda P^m}$ and $\mathbb P_\pi$ by $\|\lambda P^m - \pi\|$, and the uniform hypothesis bounds that by $C$.
-- source:
--   L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; D. A. Levin and Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Ch. 4; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Corollary 5.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

theorem MarkovChainCLT.tvDist_chainMeasure_shift_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (lam : Measure X) [IsProbabilityMeasure lam] (m : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist (iterKernel P m x) π ≤ C) :
    tvDist ((chainMeasure P lam).map (fun ω : ℕ → X => fun n => ω (n + m)))
      (chainMeasure P π) ≤ C := by sorry
