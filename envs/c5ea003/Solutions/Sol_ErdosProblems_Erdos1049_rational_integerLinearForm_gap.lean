-- Prove2me | solution 1 for ErdosProblems.Erdos1049.rational_integerLinearForm_gap
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:13:49.61147+00:00
-- url     : https://prove2.me/submissions/e5bc9b7e-221b-41c4-97e1-6071ceed5b66

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

namespace ErdosProblems.Erdos1049
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
end ErdosProblems.Erdos1049

open Filter
open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hform :
      (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) =
        ((B * a - A * q : ℤ) : ℝ) / (q : ℝ) := by
    rw [show ((B * a - A * q : ℤ) : ℝ) =
      (B : ℝ) * (a : ℝ) - (A : ℝ) * (q : ℝ) by push_cast; ring]
    calc
      (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) =
          ((B : ℝ) * (a : ℝ)) / (q : ℝ) - (A : ℝ) := by ring
      _ = ((B : ℝ) * (a : ℝ)) / (q : ℝ) -
          ((A : ℝ) * (q : ℝ)) / (q : ℝ) := by
        rw [mul_div_cancel_right₀ _ hq0]
      _ = ((B : ℝ) * (a : ℝ) - (A : ℝ) * (q : ℝ)) / (q : ℝ) := by
        rw [sub_div]
  have hnum : B * a - A * q ≠ 0 := by
    intro hzero
    apply hne
    rw [hform, hzero]
    norm_num
  have honeZ : (1 : ℤ) ≤ |B * a - A * q| := Int.one_le_abs hnum
  have honeR : (1 : ℝ) ≤ |((B * a - A * q : ℤ) : ℝ)| := by
    exact_mod_cast honeZ
  rw [hform, abs_div, abs_of_pos hqR]
  exact (div_le_div_iff_of_pos_right hqR).2 honeR
