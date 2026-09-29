-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.qPochhammerInfinity_le_finite
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:57:30.772582+00:00
-- url     : https://prove2.me/submissions/7bb8e88b-6e17-4459-b671-9059ec8ad2b0

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_summable_nonneg_dominated
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_abs_log_one_sub_le
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_hasSum_qPochhammer_log_majorant
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Positive q-products and q-binomial ratio coefficients

The infinite product is constructed from an absolutely
convergent logarithmic series, and is proved to be the limit of its finite
products. Its positivity is therefore not an assumed supplier.
-/

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology







@[simp] theorem qPochhammerFinite_zero (a q : ℝ) : qPochhammerFinite a q 0 = 1 := by
  simp [qPochhammerFinite]

theorem qPochhammerFinite_succ (a q : ℝ) (n : ℕ) :
    qPochhammerFinite a q (n + 1) = qPochhammerFinite a q n * (1 - a * q ^ n) := by
  simp [qPochhammerFinite, Finset.prod_range_succ]







/-- Absolute logarithmic convergence proves that no limiting product vanishes. -/
theorem summable_log_qPochhammer {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun k : ℕ => Real.log (1 - a * q ^ k)) := by
  apply Summable.of_abs
  apply summable_nonneg_dominated (fun _ => abs_nonneg _)
  · intro k
    apply abs_log_one_sub_le (mul_nonneg ha0 (pow_nonneg hq0 k))
    · simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) ha0
    · exact ha1
  · exact (hasSum_qPochhammer_log_majorant (a := a) hq0 hq1).summable





lemma exp_sum_log_qPochhammer {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Real.exp (∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k)) =
      qPochhammerFinite a q n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hfactor : 0 < 1 - a * q ^ n := by
      have hp : a * q ^ n ≤ a := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) ha0
      linarith
    rw [Finset.sum_range_succ, Real.exp_add, hn, Real.exp_log hfactor,
      qPochhammerFinite_succ]
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerInfinity a q ≤ qPochhammerFinite a q n := by
  have hs := summable_log_qPochhammer ha0 ha1 hq0 hq1
  have hn : ∀ k : ℕ, Real.log (1 - a * q ^ k) ≤ 0 := by
    intro k
    have hf : 0 < 1 - a * q ^ k := by
      have : a * q ^ k ≤ a := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) ha0
      linarith
    have hh := Real.log_le_log hf
      (by nlinarith [mul_nonneg ha0 (pow_nonneg hq0 k)] : 1 - a * q ^ k ≤ 1)
    simpa using hh
  have hb := hs.neg.sum_le_tsum (Finset.range n) (fun k _ => neg_nonneg.mpr (hn k))
  simp only [Finset.sum_neg_distrib, tsum_neg] at hb
  have hlogs : (∑' k : ℕ, Real.log (1 - a * q ^ k)) ≤
      ∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k) := by linarith
  calc
    qPochhammerInfinity a q ≤
        Real.exp (∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k)) :=
      Real.exp_le_exp.mpr hlogs
    _ = _ := exp_sum_log_qPochhammer ha0 ha1 hq0 hq1.le n
