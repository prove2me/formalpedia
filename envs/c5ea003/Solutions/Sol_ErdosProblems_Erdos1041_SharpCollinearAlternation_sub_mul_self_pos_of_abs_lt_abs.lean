-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearAlternation.sub_mul_self_pos_of_abs_lt_abs
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:36.40542+00:00
-- url     : https://prove2.me/submissions/f3bba49e-ad09-44f4-9830-d826a315c5df

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation
end ErdosProblems.Erdos1041.SharpCollinearAlternation

/-!
# Sharp constrained alternation for the collinear Erdős #1041 case

This module isolates the rigidity argument behind the sharp adjacent-gap
estimate.  If two monic real polynomials of the same degree agree at the two
endpoints, the second polynomial cannot be uniformly smaller than the first
at a full alternating sequence of interior peaks: otherwise their difference
has one zero between each consecutive pair of peaks as well as the two
endpoint zeros, although its degree has dropped by one.

The intended comparison polynomial is the endpoint-normalised scaled
Chebyshev polynomial.  Keeping the alternation engine independent of that
instantiation makes the root-counting step reusable and auditable.
-/

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation
open Set
open Polynomial
end ErdosProblems.Erdos1041.SharpCollinearAlternation

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation in
theorem solution {x y : ℝ} (h : |y| < |x|) :
    0 < (x - y) * x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at h
    have hxpos : 0 < x := by
      by_contra hxnot
      have : x = 0 := le_antisymm (le_of_not_gt hxnot) hx
      subst x
      exact (not_lt_of_ge (abs_nonneg y)) h
    have hylt : y < x := (abs_lt.mp h).2
    nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hxneg] at h
    have hxlt : x < y := by simpa using (abs_lt.mp h).1
    nlinarith
