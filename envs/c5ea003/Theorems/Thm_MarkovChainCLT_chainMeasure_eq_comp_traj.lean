-- Prove2me | Theorems.Thm_MarkovChainCLT_chainMeasure_eq_comp_traj
-- name    : MarkovChainCLT.chainMeasure_eq_comp_traj
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:58:55.924015+00:00
-- url     : https://prove2.me/theorems/7d108ccc-c0a7-4071-bcee-0e29a4d8a3a3
-- title:
--   Disintegration of the chain law over its first $k+1$ coordinates
-- statement:
--   Let $P$ be a Markov kernel with initial distribution $\lambda$, and let $\mathbb{P}_\lambda$ be the resulting law on path space. Then for every $k$,
--
--   $$\mathbb{P}_\lambda \;=\; \mathrm{traj}_k \circ \bigl(\mathrm{fr}_k\bigr)_*\mathbb{P}_\lambda,$$
--
--   where $\mathrm{fr}_k(\omega) = (\omega_0,\dots,\omega_k)$ and $\mathrm{traj}_k$ is the kernel sending an initial segment to the law of the trajectory continuing from it.
--
--   **What it says.** *The law of the chain is recovered by drawing its first $k+1$ coordinates from their own marginal and then continuing with $\mathrm{traj}_k$.* This is the disintegration of the path measure over the past up to time $k$ — the precise sense in which $\mathrm{traj}_k$ is the conditional law of the trajectory given $(X_0,\dots,X_k)$, and the form in which conditioning is actually applied.
--
--   **Why it is needed.** Mixing estimates all have the shape: fix a past event $A$ and a future event $B$, condition on the first $k+1$ coordinates, and compare the conditional probability of $B$ with its stationary value. The conditioning step is exactly this identity. Once it is available, a past event — which by the identification of the past $\sigma$-algebra is a pullback $\mathrm{fr}_k^{-1}(A_0)$ — becomes a *function of the integration variable* in the outer integral, while a future event is handled inside $\mathrm{traj}_k(u)$ by the restart property. Without the disintegration the two identifications have nothing to act on.
--
--   **Proof.** Two observations, both at the level of kernels. First, the marginal: pushing the trajectory kernel forward along $\mathrm{fr}_k$ gives $\mathrm{partialTraj}(0,k)$ precomposed with the embedding of a point as a length-one segment, so $(\mathrm{fr}_k)_*\mathbb{P}_\lambda = Q \circ \lambda$ for that kernel $Q$. Second, the decomposition: Mathlib's $\mathrm{traj}_0 = \mathrm{traj}_k \circ \mathrm{partialTraj}(0,k)$ together with the fact that precomposition commutes with composition on the right gives $\mathrm{traj}_k \circ Q = $ the trajectory kernel of the chain. Associativity of composition with a measure then turns $\mathrm{traj}_k \circ (Q \circ \lambda)$ into $(\mathrm{traj}_k \circ Q) \circ \lambda = \mathbb{P}_\lambda$.
--
--   No hypothesis on $\lambda$ beyond being a probability measure is needed; in particular the chain need not be started from an invariant measure.
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; O. Kallenberg, Foundations of Modern Probability, 2nd ed., Springer 2002, Ch. 6 and Ch. 8; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3.

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

theorem MarkovChainCLT.chainMeasure_eq_comp_traj {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam] (k : ℕ) :
    chainMeasure P lam
      = (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k)
          ∘ₘ ((chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k)) := by sorry
