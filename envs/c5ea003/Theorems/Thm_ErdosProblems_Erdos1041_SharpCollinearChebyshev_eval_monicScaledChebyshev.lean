-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_eval_monicScaledChebyshev
-- name    : ErdosProblems.Erdos1041.SharpCollinearChebyshev.eval_monicScaledChebyshev
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:35.844505+00:00
-- url     : https://prove2.me/theorems/f0390d9f-d3cc-4e14-9fa6-75f48dc47ccf
-- title:
--   Evaluation of the scaled monic Chebyshev polynomial
-- statement:
--   Let $n\ge2$ be an integer, $x\in\mathbb R$, $r_n=\cos(\pi/(2n))$, and $T_n$ the Chebyshev polynomial of the first kind. The monic scaled polynomial $q_n$ satisfies $q_n(x)=2^{-(n-1)}r_n^{-n}T_n(r_nx)$. This identity transports classical Chebyshev values to the endpoint-normalized comparator.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L68-L82

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

theorem ErdosProblems.Erdos1041.SharpCollinearChebyshev.eval_monicScaledChebyshev {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    (monicScaledChebyshev n).eval x =
      ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n * x) := by sorry
