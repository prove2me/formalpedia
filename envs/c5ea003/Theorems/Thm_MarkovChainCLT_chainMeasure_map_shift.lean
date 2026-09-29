-- Prove2me | Theorems.Thm_MarkovChainCLT_chainMeasure_map_shift
-- name    : MarkovChainCLT.chainMeasure_map_shift
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:18:55.166641+00:00
-- url     : https://prove2.me/theorems/295c6edc-7d3f-4de1-ae15-c05879ed4354
-- title:
--   The chain started from an invariant measure has a shift-invariant trajectory law
-- statement:
--   Let $P$ be a Markov kernel on $\mathsf{X}$ and let $\pi$ be an invariant probability measure for $P$. Let $\mathbb{P}_\pi$ denote the law on path space $\mathsf{X}^{\mathbb{N}}$ of the chain with initial distribution $\pi$, and let $\sigma$ be the shift, $\sigma(\omega)_n = \omega_{n+1}$. Then
--
--   $$\sigma_*\,\mathbb{P}_\pi \;=\; \mathbb{P}_\pi .$$
--
--   **What it says.** Starting a Markov chain from an invariant measure makes the whole *trajectory law* shift-invariant, not merely each one-dimensional marginal. Invariance of $\pi$ is a statement about a single time step, $\pi P = \pi$; shift-invariance of $\mathbb{P}_\pi$ is a statement about the entire process. The passage from one to the other is the reason "invariant measure" and "stationary distribution" are used interchangeably, and it is what licenses applying the ergodic theorem, mixing-coefficient definitions, and stationary-sequence central limit theorems to a Markov chain started from $\pi$.
--
--   **Why it needs the shift identity.** The step that does the work is time-homogeneity in the form $\sigma_*\mathbb{P}_x = \int \mathbb{P}_y\,P(x,\mathrm{d}y)$. Given that, the computation is three lines:
--   $$\sigma_*\mathbb{P}_\pi \;=\; \sigma_*\!\int \mathbb{P}_x\,\pi(\mathrm{d}x) \;=\; \int \sigma_*\mathbb{P}_x \,\pi(\mathrm{d}x)\;=\; \int\!\!\int \mathbb{P}_y P(x,\mathrm{d}y)\pi(\mathrm{d}x) \;=\; \int \mathbb{P}_y \,(\pi P)(\mathrm{d}y) \;=\; \int \mathbb{P}_y\,\pi(\mathrm{d}y) \;=\; \mathbb{P}_\pi,$$
--   the last-but-one equality being exactly the invariance of $\pi$. Everything difficult is in the shift identity, which is not available for free in a formalization built on the Ionescu–Tulcea theorem: `Kernel.traj` is constructed for a general, possibly time-inhomogeneous family, and its API never uses the fact that the one-step kernels are all the same $P$.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 10 (invariant measures and stationarity); O. Kallenberg, Foundations of Modern Probability, 2nd ed., Springer 2002, Ch. 8; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem MarkovChainCLT.chainMeasure_map_shift {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    (chainMeasure P π).map (fun ω : ℕ → X => fun n => ω (n + 1)) = chainMeasure P π := by sorry
