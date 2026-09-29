-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_sourcePositiveHTerm_bounds
-- name    : ErdosProblems.Erdos1049.PaperR10.sourcePositiveHTerm_bounds
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:58:11.444801+00:00
-- url     : https://prove2.me/theorems/0d14cb5e-8831-43e4-9b8c-70174779f439
-- title:
--   Source positive hterm bounds
-- statement:
--   For 0<q<1 and natural n,t, write P=qPochhammerInfinity(q,q). The source term HTerm(q,n,t) lies between q^((14n+1)t)P² and P⁻²(q^(14n+1))ᵗ.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourcePositiveHBoundsR10.lean#L49-L78
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

theorem ErdosProblems.Erdos1049.PaperR10.sourcePositiveHTerm_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) :
    q ^ ((14 * n + 1) * t) * (qPochhammerInfinity q q) ^ 2 ≤
        sourcePositiveHTerm q n t ∧
    sourcePositiveHTerm q n t ≤
        (qPochhammerInfinity q q)⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t := by sorry
