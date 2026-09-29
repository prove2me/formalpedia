-- Prove2me | Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_le_policy_of_unit_losses
-- name    : BanditAlgorithm.pmMinimaxRegret_le_policy_of_unit_losses
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T20:06:39.869033+00:00
-- url     : https://prove2.me/theorems/1e83d84c-65fa-41b3-b8c2-fcc7dc91933c
-- title:
--   Minimax partial-monitoring regret is bounded by any policy’s worst-case regret
-- statement:
--   Consider a finite partial-monitoring game with losses in $[0,1]$ and at least one action. For any horizon $n$ and any admissible policy $\pi$, the minimax regret is at most the worst-case regret of that policy:
--
--   $$
--   R_n^*(G)\le \sup_{i_{1:n}} R_n(\pi,i_{1:n},G).
--   $$
--
--   This is the policy-specialization principle for the infimum in the definition of minimax regret. The unit-loss assumption supplies a uniform lower bound on every policy’s worst-case regret, which is required because Lean represents the real infimum using a conditionally complete lattice. The statement also covers horizons or outcome spaces for which the set of outcome sequences is empty.
-- source:
--   Formal bridge from the definition of minimax regret in Lattimore and Szepesvári, Bandit Algorithms (2020), §37.1 p. 480 and §37.2 p. 483; used in Theorem 37.15, pp. 494–495, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Data.Fintype.Order

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

theorem pmMinimaxRegret_le_policy_of_unit_losses
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 1 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (π : PMPolicy k 𝕊) :
    pmMinimaxRegret G n ≤ ⨆ i : Fin n → Fin d, pmRegret G π n i := by sorry
