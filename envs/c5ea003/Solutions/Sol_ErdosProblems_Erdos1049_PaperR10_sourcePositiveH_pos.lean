-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.sourcePositiveH_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:01:55.96177+00:00
-- url     : https://prove2.me/submissions/98808d31-3d95-4459-ae38-885e9a1989a6

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qPochhammerInfinity_pos
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_sourcePositiveH_bounds
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
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < sourcePositiveH q n :=
  (sq_pos_of_pos (qPochhammerInfinity_pos q q)).trans_le
    (sourcePositiveH_bounds hq0 hq1 n).1
