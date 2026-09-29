-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
-- name    : ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:11.587231+00:00
-- url     : https://prove2.me/theorems/84b1ebac-aa58-467d-a68f-992b047e1a80
-- title:
--   The actual positive 2004 source series in direction (14,12,14;27)
-- statement:
--   The literal positive hypergeometric H series is constructed with its 13n+1 terminal denominator, then proved summable, uniformly bounded, and zero-rate. The submitted module contains the source declarations quotient_of_unit_interval_bounds, sourcePositiveHTerm, sourcePositiveH, sourcePositiveHTerm_bounds, sourcePositiveHTerm_nonneg, among others. Source topic: The actual positive 2004 source series in direction (14,12,14;27).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourcePositiveHBoundsR10.lean#L22-L172
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
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
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology



/-- The positive series printed in the current short paper, with every
Pochhammer length written as a natural number without truncated subtraction. -/
noncomputable def sourcePositiveHTerm (q : ℝ) (n t : ℕ) : ℝ :=
  q ^ ((14 * n + 1) * t) *
    (qPochhammerFinite (q ^ (t + 1)) q (12 * n) /
      qPochhammerFinite q q (12 * n)) *
    (qPochhammerFinite q q (13 * n) /
      qPochhammerFinite (q ^ (14 * n + 1 + t)) q (13 * n + 1))

noncomputable def sourcePositiveH (q : ℝ) (n : ℕ) : ℝ :=
  ∑' t : ℕ, sourcePositiveHTerm q n t

















end ErdosProblems.Erdos1049.PaperR10


