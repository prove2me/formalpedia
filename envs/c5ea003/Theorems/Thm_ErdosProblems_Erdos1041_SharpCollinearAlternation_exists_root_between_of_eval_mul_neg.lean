-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_exists_root_between_of_eval_mul_neg
-- name    : ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_root_between_of_eval_mul_neg
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:42.81998+00:00
-- url     : https://prove2.me/theorems/5b0a5ad1-ae90-45c3-8c51-0136a8eae70e
-- title:
--   Polynomial intermediate-value lemma
-- statement:
--   Let $p$ be a real polynomial and $a<b$ real numbers. If $p(a)p(b)<0$, then $p$ has a zero strictly between $a$ and $b$. This is the root-counting step behind the alternation bound.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearAlternation.lean#L63-L93

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

theorem ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_root_between_of_eval_mul_neg
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hneg : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by sorry
