-- Prove2me | Theorems.Thm_MarkovChainCLT_processSigma_le_of_measurable
-- name    : MarkovChainCLT.processSigma_le_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:51:24.865641+00:00
-- url     : https://prove2.me/theorems/8af9ee0e-90ea-4931-a523-423ce4aab9f2
-- title:
--   Process $\sigma$-algebras sit below ambient
-- statement:
--   Generated $\sigma$-algebras are sub-$\sigma$-algebras when coordinates are measurable.
--
--   If each $Y_i$ is measurable, then for any $s\subseteq\mathbb N$, $\sigma(Y_i:i\in s)\le\mathcal F$, since each pullback is below $\mathcal F$ and suprema preserve the order.
--
--   **Formalization Note** `processSigma` is the supremum of pullbacks.
-- source:
--   Lattice property; used for condExp and Fubini over past/future

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.processSigma_le_of_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (Y : ℕ → Ω → E) (hY : ∀ n, Measurable (Y n)) (s : Set ℕ) : processSigma Y s ≤ ‹MeasurableSpace Ω› := by sorry
