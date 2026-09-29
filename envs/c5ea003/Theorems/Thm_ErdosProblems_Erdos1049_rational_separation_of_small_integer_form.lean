-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_rational_separation_of_small_integer_form
-- name    : ErdosProblems.Erdos1049.rational_separation_of_small_integer_form
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:13:36.143674+00:00
-- url     : https://prove2.me/theorems/6ccb82fd-2bbc-4f9d-8f24-fc0badd06d37
-- title:
--   Rational separation of small integer form
-- statement:
--   For integer A,B,p,q with q>0, if 2q|Aξ−B|≤1, then |Aξ−B|≤|A|·|ξ−p/q|.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/RationalApproximationSeparation.lean#L13-L48
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


Finite separation at a rational test point. The result uses the already
present rational_integerLinearForm_gap, handles the zero determinant case,
and avoids requiring two independent approximating rows. The asymptotic
source estimates needed for an irrationality measure are not proved here.
-/

open ErdosProblems.Erdos1049

theorem ErdosProblems.Erdos1049.rational_separation_of_small_integer_form
    (A B p q : ℤ) (ξ : ℝ) (hq : 0 < q)
    (hsmall : 2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤ 1) :
    |(A : ℝ) * ξ - B| ≤
      |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by sorry
