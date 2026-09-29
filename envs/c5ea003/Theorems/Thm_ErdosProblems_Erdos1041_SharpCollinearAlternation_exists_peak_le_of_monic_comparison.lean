-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_exists_peak_le_of_monic_comparison
-- name    : ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_peak_le_of_monic_comparison
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:57.10246+00:00
-- url     : https://prove2.me/theorems/4e72cc5f-867c-481b-920f-81bc7d0cea5d
-- title:
--   Alternation bound against a monic comparator
-- statement:
--   Let $p,u$ be monic real polynomials of degree $n+2$, both zero at endpoints $a<b$. Let $c_0<\cdots<c_n$ lie strictly between the endpoints, assume the values of $p$ alternate in sign at successive $c_i$, and assume $|u(c_i)|\le C$ at every point. Then $|p(c_i)|\le C$ for at least one $i$. This is the abstract comparison principle used with the Chebyshev polynomial.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearAlternation.lean#L154-L192

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

theorem ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_peak_le_of_monic_comparison
    {n : ℕ} {p u : ℝ[X]} {a b C : ℝ} {c : Fin (n + 1) → ℝ}
    (hp : p.IsMonicOfDegree (n + 2)) (hu : u.IsMonicOfDegree (n + 2))
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (hua : u.eval a = 0) (hub : u.eval b = 0)
    (hpalt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hubound : ∀ i : Fin (n + 1), |u.eval (c i)| ≤ C) :
    ∃ i : Fin (n + 1), |p.eval (c i)| ≤ C := by sorry
