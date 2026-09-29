-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_sub_mul_self_pos_of_abs_lt_abs
-- name    : ErdosProblems.Erdos1041.SharpCollinearAlternation.sub_mul_self_pos_of_abs_lt_abs
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:50.290317+00:00
-- url     : https://prove2.me/theorems/1d61c53e-9783-42db-b3f5-5639429ef462
-- title:
--   Sign retained under a smaller perturbation
-- statement:
--   For real numbers $x,y$ with $|y|<|x|$, the product $(x-y)x$ is positive. This simple inequality transfers the sign of an alternating comparison value to a polynomial difference.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearAlternation.lean#L29-L45

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


open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation

theorem ErdosProblems.Erdos1041.SharpCollinearAlternation.sub_mul_self_pos_of_abs_lt_abs {x y : ℝ} (h : |y| < |x|) :
    0 < (x - y) * x := by sorry
