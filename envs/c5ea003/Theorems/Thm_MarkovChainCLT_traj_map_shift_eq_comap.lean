-- Prove2me | Theorems.Thm_MarkovChainCLT_traj_map_shift_eq_comap
-- name    : MarkovChainCLT.traj_map_shift_eq_comap
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:41:10.583634+00:00
-- url     : https://prove2.me/theorems/38997813-bec4-4bf1-865b-b5db64c281d9
-- title:
--   Strong restart: given the past, the future is a fresh chain started at the last state
-- statement:
--   Let $P$ be a Markov kernel on $\mathsf{X}$ and let $\mathrm{traj}_j$ denote the Ionescu–Tulcea kernel that, given an initial segment $u = (u_0,\dots,u_j)$, returns the law of the whole trajectory continuing from it. Let $\sigma^j$ be the shift $(\sigma^j\omega)_n = \omega_{j+n}$. Then
--
--   $$\sigma^j_*\bigl[\mathrm{traj}_j(u)\bigr] \;=\; \mathbb{P}_{u_j},$$
--
--   i.e. as an identity of kernels, pushing the conditional trajectory kernel forward along the $j$-shift gives the trajectory kernel of the chain, precomposed with "read off the last coordinate".
--
--   **The strong restart property.** In words: *conditionally on the first $j+1$ states $(X_0,\dots,X_j) = u$, the future $(X_j, X_{j+1}, \dots)$ is a copy of the chain started afresh at $u_j$, and in particular depends on $u$ only through $u_j$.* This is the Markov property in the form that quantitative arguments actually consume, and it is strictly stronger than the unconditional shift identity $\sigma_*\mathbb{P}_x = \int \mathbb{P}_y P(x,\mathrm{d}y)$: the latter describes the law of a shifted trajectory averaged over everything, while this describes it *given the entire past*, and asserts that the past is forgotten apart from its final state.
--
--   **Why it is the gateway to mixing estimates.** All three classical mixing coefficients compare the past $\sigma(X_0,\dots,X_k)$ with the future $\sigma(X_{k+n}, X_{k+n+1},\dots)$. Bounding them requires expressing the conditional law of the future given the past, and this theorem is exactly that expression: combined with the decomposition $\mathrm{traj}_0 = \mathrm{traj}_j \circ \mathrm{partialTraj}(0,j)$, it says that conditioning on the first $j+1$ coordinates and then looking $n$ steps ahead yields the chain started from $P^n(u_j,\cdot)$. A total-variation rate $\|P^n(x,\cdot)-\pi\| \le C$ then bounds the mixing coefficient at lag $n$ by $C$, uniformly in the split point.
--
--   **Proof.** By the fact that a path measure is determined by its finite-dimensional marginals, it suffices to check agreement after restricting to each initial segment $\mathrm{Iic}\,m$. On the left, $\mathrm{fr}_m \circ \sigma^j = \sigma^j_{\mathrm{fin}} \circ \mathrm{fr}_{j+m}$ — an identity that holds *definitionally* with the length written as $j+m$ — so the left marginal is the $j$-shift pushforward of $\mathrm{partialTraj}(j, j{+}m)$. On the right it is $\mathrm{partialTraj}(0,m)$ precomposed with $u \mapsto u_j$. The two are identified by induction on $m$: the base case is the observation that shifting a length-$(j{+}1)$ segment down to length one just reads off $u_j$, and the inductive step splits $\mathrm{partialTraj}(j, j{+}m{+}1)$ as one step after $\mathrm{partialTraj}(j, j{+}m)$ and applies the arbitrary-offset time-homogeneity lemma to move the shift past that step.
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3; C. J. Geyer, "Practical Markov Chain Monte Carlo", Statistical Science 7 (1992) 473-483, Section 3; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.traj_map_shift_eq_comap {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (j : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) j).map
        (fun ω : ℕ → S => fun n => ω (j + n))
      = (BanditAlgorithm.markovChainKernel P).comap (fun u : Π _i : Finset.Iic j, S =>
          u ⟨j, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by sorry
