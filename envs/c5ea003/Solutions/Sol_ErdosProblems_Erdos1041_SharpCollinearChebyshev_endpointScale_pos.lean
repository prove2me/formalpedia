-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:49:09.544593+00:00
-- url     : https://prove2.me/submissions/51afa671-621b-4403-927a-406e8680ba03

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
    0 < endpointScale n := by
  apply Real.cos_pos_of_mem_Ioo
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (2 : ℝ) * n := by positivity
  have hangle : 0 < Real.pi / ((2 : ℝ) * n) :=
    div_pos Real.pi_pos hden
  constructor
  · linarith [Real.pi_pos]
  · have hdenlt : (2 : ℝ) < 2 * n := by nlinarith
    have hinv : (1 : ℝ) / (2 * n) < 1 / 2 :=
      one_div_lt_one_div_of_lt (by norm_num) hdenlt
    calc
      Real.pi / (2 * (n : ℝ)) = Real.pi * (1 / (2 * n)) := by ring
      _ < Real.pi * (1 / 2) := mul_lt_mul_of_pos_left hinv Real.pi_pos
      _ = Real.pi / 2 := by ring
