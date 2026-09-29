-- Prove2me | Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift_iter
-- name    : MarkovChainCLT.markovChainKernel_map_shift_iter
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:29:22.714956+00:00
-- url     : https://prove2.me/theorems/270e7183-0d19-4afe-9e97-1e827fa41e32
-- title:
--   Discarding the first $k$ steps restarts the chain from $P^k$
-- statement:
--   Let $P$ be a Markov kernel on $\mathsf{X}$, let $\mathbb{P}_x$ be the law of the trajectory started at $x$, and let $\sigma^k$ be the $k$-fold shift on path space, $(\sigma^k\omega)_n = \omega_{n+k}$. Then for every $k$,
--
--   $$\sigma^k_*\,\mathbb{P}_x \;=\; \int_{\mathsf{X}} \mathbb{P}_y \; P^k(x,\mathrm{d}y),$$
--
--   i.e. as an identity of kernels, the pushforward of the trajectory kernel along the $k$-shift is its composition with the $k$-step transition kernel $P^k$.
--
--   **What it says.** *Discarding the first $k$ observations of a Markov chain started at $x$ leaves a Markov chain started from the $k$-step distribution $P^k(x,\cdot)$.* This is the "restart" or regeneration principle in its simplest, unconditional form, and it is the workhorse behind every quantitative mixing estimate: bounding the dependence between the past $\sigma(X_0,\dots,X_j)$ and the future $\sigma(X_{j+k},X_{j+k+1},\dots)$ always proceeds by re-expressing the future as a chain restarted from $P^k(\cdot,\cdot)$ and then invoking a rate of convergence $\|P^k(x,\cdot) - \pi\|$.
--
--   **Proof.** Induction on $k$, with the one-step identity $\sigma_*\mathbb{P}_x = \int \mathbb{P}_y P(x,\mathrm{d}y)$ as the base mechanism. The key bookkeeping is the factorisation $\sigma^{k+1} = \sigma^k \circ \sigma$, which holds *definitionally* in this indexing (unlike the equally true $\sigma \circ \sigma^k$, since addition on $\mathbb{N}$ recurses on its second argument). Pushing forward along $\sigma$ first turns the trajectory kernel into its composition with $P$; the induction hypothesis then handles $\sigma^k$, and reassociating leaves $P^k \circ P$. A short separate induction shows $P^k \circ P = P \circ P^k$, which converts this into $P^{k+1}$ as defined by the recursion $P^{k+1} = P \circ P^k$.
--
--   That commutation step is not a triviality to be skipped: with $P^{k+1}$ *defined* as $P \circ P^k$, the composite produced by the shift argument is $P^k \circ P$, and identifying the two is exactly the statement that the $k$-step kernel can be built by taking the extra step either at the beginning or at the end.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3 and Ch. 16; C. J. Geyer, "Practical Markov Chain Monte Carlo", Statistical Science 7 (1992) 473-483, Section 3; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem MarkovChainCLT.markovChainKernel_map_shift_iter {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (k : ℕ) :
    (BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => fun n => ω (n + k))
      = (BanditAlgorithm.markovChainKernel P) ∘ₖ (iterKernel P k) := by sorry
