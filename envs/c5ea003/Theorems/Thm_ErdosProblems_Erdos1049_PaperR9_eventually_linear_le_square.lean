-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_eventually_linear_le_square
-- name    : ErdosProblems.Erdos1049.PaperR9.eventually_linear_le_square
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:15:07.111177+00:00
-- url     : https://prove2.me/theorems/4ef95457-912a-4b9b-a8d9-3544c9c97b4f
-- title:
--   Eventually linear le square
-- statement:
--   For C≥0 and ε>0, the linear error C(2n+1) is eventually at most εn².
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperAsymptoticsR9.lean#L130-L148
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Quadratic asymptotic transfer, revision of the round-8 return.
Compiled. This file contains proof text, not a kernel receipt.

The asymptotic hypotheses below are estimates, not assumptions of the conclusions.
In particular `cross_product_limits` proves both successor products. The integer
contradiction is the desk's repaired PaperRankTwoCapR7 theorem, reused unchanged.

Pinned API: Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
Filter/metric API: Order/Filter/AtTopBot/Basic.lean and
Topology/MetricSpace/Pseudo/Defs.lean. Exponential/log API:
Analysis/SpecialFunctions/Exp.lean and Log/Basic.lean. Elementary ordered-field
algebra is handled by ring, linarith and explicitly supplied polynomial facts.
-/
open Filter Asymptotics
open scoped Topology

open ErdosProblems.Erdos1049.PaperR9

theorem ErdosProblems.Erdos1049.PaperR9.eventually_linear_le_square (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (2 * (n : ℝ) + 1) ≤ ε * sqScale n := by sorry
