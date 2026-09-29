-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearChebyshev.eval_monicScaledChebyshev
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:30.504985+00:00
-- url     : https://prove2.me/submissions/44831753-bd61-4f6b-b2dd-10c50f8fe4c0

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
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

namespace ErdosProblems.Erdos1041.SharpCollinearChebyshev
open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation









theorem endpointScale_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    endpointScale n ≠ 0 :=
  (endpointScale_pos hn).ne'
end ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation
open ErdosProblems.Erdos1041.SharpCollinearChebyshev in
theorem solution {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    (monicScaledChebyshev n).eval x =
      ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n * x) := by
  have hr := endpointScale_ne_zero hn
  have hscale := Polynomial.scaleRoots_eval_mul
    (Polynomial.Chebyshev.T ℝ (n : ℤ)) (endpointScale n * x) (endpointScale n)⁻¹
  have hscale' :
      ((Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹).eval x =
        (endpointScale n)⁻¹ ^ n *
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n * x) := by
    simpa [Polynomial.Chebyshev.natDegree_T, hr, mul_assoc] using hscale
  simp [monicScaledChebyshev, eval_mul, hscale', mul_assoc]
