-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_root_between_of_eval_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:35.331591+00:00
-- url     : https://prove2.me/submissions/ec8dcd0d-160c-47c8-9f13-783b1f59adfe

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
theorem solution
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hneg : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hneg with hsign | hsign
  · obtain ⟨x, hx⟩ := (Set.mem_image (fun t : ℝ ↦ p.eval t) (Icc a b) 0).mp
        (intermediate_value_Icc' hab.le p.continuous.continuousOn
          (show 0 ∈ Icc (p.eval b) (p.eval a) by exact ⟨hsign.2.le, hsign.1.le⟩))
    have hax : a < x := lt_of_le_of_ne hx.1.1 (by
      intro hEq
      subst x
      linarith [hsign.1, hx.2])
    have hxb : x < b := lt_of_le_of_ne hx.1.2 (by
      intro hEq
      subst x
      linarith [hsign.2, hx.2])
    exact ⟨x, ⟨hax, hxb⟩, hx.2⟩
  · obtain ⟨x, hx⟩ := (Set.mem_image (fun t : ℝ ↦ p.eval t) (Icc a b) 0).mp
        (intermediate_value_Icc hab.le p.continuous.continuousOn
          (show 0 ∈ Icc (p.eval a) (p.eval b) by exact ⟨hsign.1.le, hsign.2.le⟩))
    have hax : a < x := lt_of_le_of_ne hx.1.1 (by
      intro hEq
      subst x
      linarith [hsign.1, hx.2])
    have hxb : x < b := lt_of_le_of_ne hx.1.2 (by
      intro hEq
      subst x
      linarith [hsign.2, hx.2])
    exact ⟨x, ⟨hax, hxb⟩, hx.2⟩
