-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev_isMonicOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:31.458935+00:00
-- url     : https://prove2.me/submissions/6ed53e92-5384-4f9e-8100-ab6de16e8d19

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

namespace ErdosProblems.Erdos1041.SharpCollinearChebyshev
open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation
end ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation
open ErdosProblems.Erdos1041.SharpCollinearChebyshev in
theorem solution {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).IsMonicOfDegree n := by
  have ha : ((2 : ℝ) ^ (n - 1))⁻¹ ≠ 0 := by positivity
  constructor
  · simp [monicScaledChebyshev, Polynomial.natDegree_C_mul ha,
      Polynomial.Chebyshev.natDegree_T]
  · rw [Polynomial.Monic]
    simp [monicScaledChebyshev, Polynomial.leadingCoeff_mul,
      Polynomial.Chebyshev.leadingCoeff_T]
