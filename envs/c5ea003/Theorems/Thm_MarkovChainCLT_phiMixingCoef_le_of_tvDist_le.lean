-- Prove2me | Theorems.Thm_MarkovChainCLT_phiMixingCoef_le_of_tvDist_le
-- name    : MarkovChainCLT.phiMixingCoef_le_of_tvDist_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T17:55:29.104574+00:00
-- url     : https://prove2.me/theorems/dd239628-578e-46c1-85d2-57c8b5d7edf9
-- title:
--   For a stationary chain, $\varphi(n)$ is controlled by the $n$-step total variation distance
-- statement:
--   Let $P$ be a Markov kernel with invariant probability $\pi$, and run the chain from $\pi$ so that it is stationary. If the $n$-step transition kernel is uniformly close to $\pi$ in total variation,
--
--   $$\sup_x \|P^n(x,\cdot) - \pi\| \le C,$$
--
--   then the uniform ($\varphi$-) mixing coefficient at lag $n$ satisfies $\varphi(n) \le C$.
--
--   **Why this is the whole Markov-property content.** By definition $\varphi(n)$ is a supremum over pairs $(A, B)$ with $A$ in the past $\sigma(X_0,\dots,X_k)$ and $B$ in the future $\sigma(X_{k+n}, X_{k+n+1}, \dots)$. The Markov property collapses this to a statement about two plain sets: conditioning on the whole past reduces to conditioning on the current state $X_k$, so $\Pr(B \mid \mathcal{F}_k) = (P^n g)(X_k)$ where $g(y) = \Pr_y(B \text{ shifted})$ takes values in $[0,1]$, and stationarity gives $\Pr(B) = \int P^n g \,\mathrm{d}\pi = \int g \,\mathrm{d}\pi$. Hence
--
--   $$\left|\frac{\Pr(A \cap B)}{\Pr(A)} - \Pr(B)\right|
--   = \frac{\left|E\bigl[\mathbf{1}_A\,\bigl((P^n g)(X_k) - \pi(g)\bigr)\bigr]\right|}{\Pr(A)}
--   \;\le\; \sup_x \left|\int g\,\mathrm{d}P^n(x,\cdot) - \int g\,\mathrm{d}\pi\right|
--   \;\le\; \sup_x \|P^n(x,\cdot) - \pi\|,$$
--
--   the last step because $0 \le g \le 1$ and the norm is the $\sup_A |\mu(A) - \nu(A)|$ normalization. This is exactly the two-set formula for $\varphi_n$ that the Markov chain literature uses in place of the general definition (see e.g. Geyer's Stat 8112 notes, eq. (34)).
--
--   Stated with an explicit uniform bound $C$ rather than a supremum, so that it composes directly: under uniform ergodicity one takes $C = R t^n$ and reads off $\varphi(n) = O(e^{-\theta n})$, which is the quantitative half of Theorem 2(iv) and the hypothesis Corollary 5 consumes.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 3, Definition 3 and Theorem 2(4) (arXiv v2 pp. 7-8); the two-set form of phi_n for a stationary Markov chain is eq. (34) in C. J. Geyer, Stat 8112 Lecture Notes: Markov Chains (2012), https://www.stat.umn.edu/geyer/8112/notes/markov.pdf; original source Ibragimov & Linnik (1971), pp. 365-366.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.phiMixingCoef_le_of_tvDist_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist ((iterKernel P n) x) π ≤ C) :
    phiMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ C := by sorry
