-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_rational_integerLinearForm_gap
-- name    : ErdosProblems.Erdos1049.rational_integerLinearForm_gap
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:13:33.446991+00:00
-- url     : https://prove2.me/theorems/d2acf587-fc04-4c52-95cb-61b0a4b843b2
-- title:
--   Rational integer linear form gap
-- statement:
--   For positive integer q, a nonzero integer form B(a/q)−A has absolute value at least 1/q.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/TwoSelectorRemainderEscape.lean#L125-L157
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace ErdosProblems.Erdos1049
end ErdosProblems.Erdos1049

/-!
# Erdős #1049: two-selector analytic-nullspace escape

Two modular selector collisions can evade the same analytic remainder
nullspace only if their exact coefficient-pair sums are collinear.  The theorem
below is the source-independent algebraic consumer of the computational
rank-two certificate.
-/


open Filter



/-! ## The rational gap behind the analytic-aware recombination

The continued-fraction recombination in `QAperyJointLocalRealLatticeLab.md`
acts by an integral unimodular matrix on two coefficient rows.  The following
lemmas isolate its exact logical reach.  Unimodularity preserves
non-collinearity, but at a rational target every nonzero integral linear form
has a fixed denominator gap.  Consequently, proving that both recombined
forms tend to zero already proves irrationality; coefficient-height control
alone cannot supply that decay.
-/

open ErdosProblems.Erdos1049

theorem ErdosProblems.Erdos1049.rational_integerLinearForm_gap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by sorry
