-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_monicScaledChebyshev_isMonicOfDegree
-- name    : ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev_isMonicOfDegree
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:45:32.352223+00:00
-- url     : https://prove2.me/theorems/54312dd4-c814-48a9-81ac-9c21c2be1dd5
-- title:
--   Degree and monicity of the scaled comparator
-- statement:
--   For every integer $n\ge2$, the endpoint-normalized scaled Chebyshev polynomial is monic of degree $n$. It can therefore be compared with any other monic degree-$n$ polynomial without leaving a leading term in their difference.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L84-L93

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# The sharp Chebyshev comparator for collinear Erdos #1041

For degree `n`, put `r = cos (pi / (2n))`.  The polynomial

`T_n(r X) / (2^(n-1) r^n)`

is monic, vanishes at `-1` and `1`, and has absolute value at most

`1 / (2^(n-1) r^n)`

on `[-1,1]`.  Combining these facts with the constrained alternation theorem
gives the sharp upper bound for one of the alternating interior peaks of any
monic comparison polynomial with the same endpoint zeros.
-/


open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation

open ErdosProblems.Erdos1041.SharpCollinearChebyshev

theorem ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev_isMonicOfDegree {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).IsMonicOfDegree n := by sorry
