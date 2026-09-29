-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
-- name    : ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale_pos
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:19.291985+00:00
-- url     : https://prove2.me/theorems/a5bdc9bc-f8b1-4c65-b1e8-3cd7d6d0cd52
-- title:
--   Positive Chebyshev endpoint scale
-- statement:
--   For an integer $n\ge2$, put $r_n=\cos(\pi/(2n))$. Then $r_n>0$. This keeps the scaling in the Chebyshev comparison nondegenerate.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L47-L62

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

theorem ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < endpointScale n := by sorry
