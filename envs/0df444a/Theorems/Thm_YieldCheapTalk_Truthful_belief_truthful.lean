-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_belief_truthful
-- name    : YieldCheapTalk.Truthful.belief_truthful
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:40.469996+00:00
-- url     : https://prove2.me/theorems/db8eaea0-adf0-4389-9926-e222726dbc8e
-- title:
--   §3, p. 9 — in any truth-revealing equilibrium the buyer's posterior belief is β(t|t, m) = 1
-- statement:
--   Consider the two-type random-yield cheap-talk model under its standing assumptions, and suppose that the ordering strategy $Q^*$ and the beliefs $\beta$ form, together with the truthful messaging strategy $r(t) = t$, a perfect Bayesian equilibrium. Then for every type $t \in T$ and every market state $m \in M$,
--   $$\beta(t\mid t, m) = 1 .$$
--   In words: in a truth-revealing equilibrium the supplier's type is credibly communicated, since every message is on the equilibrium path and Bayes' rule assigns it to the type that sends it.
--
--   This is the first step in reducing a truth-revealing equilibrium to the buyer's symmetric-information problem.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), p. 9, §3 (consequence of part (iii) of the PBE definition)

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem belief_truthful (M : Model) (hM : M.Standing) (Q : Level → Level → ℝ)
    (beta : Level → Level → Level → ℝ) (h : M.IsPBE id Q beta) :
    ∀ t m, beta t t m = 1 := by sorry
end YieldCheapTalk.Truthful
