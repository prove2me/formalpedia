-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_sourcePositiveH_bounds
-- name    : ErdosProblems.Erdos1049.PaperR10.sourcePositiveH_bounds
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:58:32.891453+00:00
-- url     : https://prove2.me/theorems/dab1f209-6450-40ce-99ff-a7f3bf06bd34
-- title:
--   Source positive h bounds
-- statement:
--   For 0<q<1 and natural n, write P=qPochhammerInfinity(q,q). The source series H(q,n) satisfies P²≤H(q,n)≤P⁻²/(1−q^(14n+1)).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourcePositiveHBoundsR10.lean#L96-L117
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The actual positive 2004 source series in direction (14,12,14;27)

This module CONSTRUCTS the positive hypergeometric series,
proves its convergence, proves uniform two-sided bounds, and proves its exact
zero quadratic logarithmic rate. In particular none of those properties is
an added hypothesis.

The last denominator has length 13*n+1. Replacing it by 13*n would be the
historical off-by-one error identified in the supplied notes.

The identity with the cancelled integer polynomial linear form is not asserted
here: that algebraic/arithmetic source transport remains separately identified.
-/
open Filter
open scoped BigOperators Topology

open ErdosProblems.Erdos1049.PaperR10

theorem ErdosProblems.Erdos1049.PaperR10.sourcePositiveH_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerInfinity q q) ^ 2 ≤ sourcePositiveH q n ∧
      sourcePositiveH q n ≤ (qPochhammerInfinity q q)⁻¹ ^ 2 /
        (1 - q ^ (14 * n + 1)) := by sorry
