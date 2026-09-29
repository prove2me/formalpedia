-- Prove2me | Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift
-- name    : MarkovChainCLT.markovChainKernel_map_shift
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T16:28:17.133753+00:00
-- url     : https://prove2.me/theorems/475be19c-8025-4b6b-8eaa-83bc45a9c0b9
-- title:
--   Time-homogeneity: shifting the trajectory is one step of $P$
-- statement:
--   Let $P$ be a Markov transition kernel on $\mathsf{X}$ and let $\mathbb{P}_x$ denote the law of the trajectory $(X_0, X_1, X_2, \dots)$ of the time-homogeneous Markov chain started at $X_0 = x$. Write $\sigma$ for the shift on path space, $\sigma(\omega)_n = \omega_{n+1}$. Then
--
--   $$\sigma_*\,\mathbb{P}_x \;=\; \int_{\mathsf{X}} \mathbb{P}_y \; P(x, \mathrm{d}y)
--   \qquad\text{for every } x,$$
--
--   i.e. **shifting the trajectory by one time step is the same as taking one step of $P$ first and then running the chain**. Equivalently, as an identity of kernels $\mathsf{X} \to \mathsf{X}^{\mathbb{N}}$, the pushforward of the trajectory kernel along $\sigma$ equals its composition with $P$.
--
--   This is the formal content of *time-homogeneity* of the chain. It is intuitively obvious and is used silently throughout the Markov chain literature, but it is not available for free in a formalization built on the Ionescu-Tulcea theorem: `Kernel.traj` is constructed for a general, possibly time-**inhomogeneous** family $\kappa_n$, and its API (`traj_comp_partialTraj`, `map_traj_succ_self`, `traj_map_frestrictLe`) never refers to the special structure of the constant family. Nothing in it transports the fact that the mission's one-step kernels satisfy $\kappa_m = P \circ \mathrm{eval}_m$ for *every* $m$. Proving the identity means comparing all finite-dimensional marginals, via an `eq_traj`-style argument together with the `partialTraj` recursion.
--
--   **Why this is worth isolating.** It is the single missing ingredient beneath several other targets of this mission. Most directly, shift-invariance of the chain started from an invariant distribution — i.e. strict stationarity of the coordinate process — follows from it in a few lines: pushing the identity through $\pi$ gives
--
--   $$\sigma_*(\mathbb{P}_\pi) = \mathbb{P}_{\pi P} = \mathbb{P}_\pi,$$
--
--   and an induction on the shift amount, using $\sigma^{k+1} = \sigma \circ \sigma^k$, gives invariance under every shift. It is also the engine of the conditional-expectation argument that bounds the strong mixing coefficients of the chain by its total-variation convergence rate, and of the transfer of a central limit theorem from the stationary start to an arbitrary initial distribution.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Sections 1-3: the chain is time-homogeneous throughout, and stationarity of the chain started from pi (used for the mixing coefficients of Section 3 and Theorems 3, 5-8) is exactly shift-invariance of the path law. See also Meyn & Tweedie (1993), Markov Chains and Stochastic Stability, Ch. 3.

import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.markovChainKernel_map_shift {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] :
    (BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => fun n => ω (n + 1))
      = (BanditAlgorithm.markovChainKernel P) ∘ₖ P := by sorry
