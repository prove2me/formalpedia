-- Prove2me | solution 1 for ErdosProblems.Erdos1049.rational_separation_of_small_integer_form
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:14:26.544698+00:00
-- url     : https://prove2.me/submissions/1d452a3a-fe31-4c87-a4dd-17ea0cd003b9

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Theorems.Thm_ErdosProblems_Erdos1049_rational_integerLinearForm_gap
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

open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution
    (A B p q : ℤ) (ξ : ℝ) (hq : 0 < q)
    (hsmall : 2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤ 1) :
    |(A : ℝ) * ξ - B| ≤
      |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hz : (A : ℝ) * ((p : ℝ) / (q : ℝ)) - B = 0
  · have hid : (A : ℝ) * ξ - B =
        (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) := by
      calc
        (A : ℝ) * ξ - B =
            (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) +
              ((A : ℝ) * ((p : ℝ) / (q : ℝ)) - B) := by ring
        _ = (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) := by rw [hz]; ring
    exact le_of_eq (by rw [hid, abs_mul])
  · have hgap := rational_integerLinearForm_gap p q B A hq hz
    have hhalf : 2 * |(A : ℝ) * ξ - B| ≤ (1 : ℝ) / q := by
      apply (le_div_iff₀ hqR).2
      nlinarith [hsmall]
    have htriangle :
        |(A : ℝ) * ((p : ℝ) / (q : ℝ)) - B| ≤
          |(A : ℝ) * ξ - B| +
            |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
      calc
        |(A : ℝ) * ((p : ℝ) / (q : ℝ)) - B| =
            |((A : ℝ) * ξ - B) -
              (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ))| := by
                congr 1
                ring
        _ ≤ |(A : ℝ) * ξ - B| +
              |(A : ℝ) * (ξ - (p : ℝ) / (q : ℝ))| := abs_sub _ _
        _ = |(A : ℝ) * ξ - B| +
              |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by rw [abs_mul]
    linarith
