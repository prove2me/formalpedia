-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_eq_zero_of_endpoint_zeros_and_alternation
-- name    : ErdosProblems.Erdos1041.SharpCollinearAlternation.eq_zero_of_endpoint_zeros_and_alternation
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:49.506852+00:00
-- url     : https://prove2.me/theorems/82dadf77-c378-4f89-a987-4ec2bafac957
-- title:
--   Too many alternating zeros force the zero polynomial
-- statement:
--   Let $p$ be a real polynomial of degree less than $n+2$. Suppose it vanishes at two endpoints $a<b$ and changes sign between each successive pair of $n+1$ strictly ordered interior points. Then $p=0$. The endpoint zeros and intervening sign changes leave no room for a nonzero polynomial of that degree.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearAlternation.lean#L95-L152

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

theorem ErdosProblems.Erdos1041.SharpCollinearAlternation.eq_zero_of_endpoint_zeros_and_alternation
    {n : ℕ} {p : ℝ[X]} {a b : ℝ} {c : Fin (n + 1) → ℝ}
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (halt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hdeg : p.natDegree < n + 2) :
    p = 0 := by sorry
