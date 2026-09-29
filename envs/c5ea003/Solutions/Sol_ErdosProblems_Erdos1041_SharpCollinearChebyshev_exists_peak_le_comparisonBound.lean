-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T04:00:03.634243+00:00
-- url     : https://prove2.me/submissions/8c7dbdff-b120-4aea-ba13-6e77916367f4

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_eval_monicScaledChebyshev
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_monicScaledChebyshev_isMonicOfDegree
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_exists_peak_le_of_monic_comparison
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















private theorem eval_chebyshev_endpointScale {n : ℕ} (hn : 2 ≤ n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [endpointScale, Polynomial.Chebyshev.T_real_cos]
  rw [show ((n : ℤ) : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 by
    norm_num
    field_simp]
  exact Real.cos_pi_div_two

theorem eval_monicScaledChebyshev_one {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).eval 1 = 0 := by
  rw [eval_monicScaledChebyshev hn]
  simp [eval_chebyshev_endpointScale hn]

theorem eval_monicScaledChebyshev_neg_one {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).eval (-1) = 0 := by
  rw [eval_monicScaledChebyshev hn]
  rw [show endpointScale n * (-1 : ℝ) = -endpointScale n by ring,
    Polynomial.Chebyshev.T_eval_neg]
  simp [eval_chebyshev_endpointScale hn]

/-- Uniform sharp comparison bound on the normalised root interval. -/
theorem abs_eval_monicScaledChebyshev_le {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : |x| ≤ 1) :
    |(monicScaledChebyshev n).eval x| ≤ comparisonBound n := by
  have hrpos := endpointScale_pos hn
  have hrle : endpointScale n ≤ 1 := Real.cos_le_one _
  have hrx : |endpointScale n * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos hrpos]
    exact mul_le_one₀ hrle (abs_nonneg x) hx
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hrx
  rw [eval_monicScaledChebyshev hn, abs_mul]
  exact (mul_le_mul_of_nonneg_left hT (abs_nonneg _)).trans_eq (by
    simp [comparisonBound])
end ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation
open ErdosProblems.Erdos1041.SharpCollinearChebyshev in
theorem solution
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  apply exists_peak_le_of_monic_comparison hp
    (monicScaledChebyshev_isMonicOfDegree (n := m + 2) (Nat.le_add_left 2 m))
    hc ha hb hpa hpb
    (eval_monicScaledChebyshev_neg_one (n := m + 2) (Nat.le_add_left 2 m))
    (eval_monicScaledChebyshev_one (n := m + 2) (Nat.le_add_left 2 m))
    hpalt
  intro i
  exact abs_eval_monicScaledChebyshev_le (n := m + 2) (Nat.le_add_left 2 m) (hc_mem i)
