-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.shifted_qPochhammer_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:58:17.820622+00:00
-- url     : https://prove2.me/submissions/72b79278-cda0-430d-bc12-6b6b3a970ddc

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qpow_antitone
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qPochhammerInfinity_le_finite
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

theorem qPochhammerFinite_nonneg_le_one {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    0 ≤ qPochhammerFinite a q n ∧ qPochhammerFinite a q n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hpow1 : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
    have hmul : 0 ≤ a * q ^ n := mul_nonneg ha0 hpow
    have hmul1 : a * q ^ n ≤ 1 := by
      calc
        a * q ^ n ≤ a * 1 := mul_le_mul_of_nonneg_left hpow1 ha0
        _ ≤ 1 := by simpa using ha1
    rw [qPochhammerFinite_succ]
    constructor
    · exact mul_nonneg hn.1 (by linarith)
    · calc
        _ ≤ 1 * (1 - a * q ^ n) :=
          mul_le_mul_of_nonneg_right hn.2 (by linarith)
        _ ≤ 1 := by nlinarith
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s n : ℕ) (hs : 1 ≤ s) :
    qPochhammerInfinity q q ≤ qPochhammerFinite (q ^ s) q n ∧
      qPochhammerFinite (q ^ s) q n ≤ 1 := by
  have hqs : q ^ s ≤ q := by simpa using qpow_antitone hq0.le hq1.le hs
  constructor
  · apply (qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 n).trans
    unfold qPochhammerFinite
    apply Finset.prod_le_prod
    · intro k hk
      have h : q * q ^ k ≤ q := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0.le hq1.le) hq0.le
      linarith
    · intro k hk
      have h := mul_le_mul_of_nonneg_right hqs (pow_nonneg hq0.le k)
      linarith
  · exact (qPochhammerFinite_nonneg_le_one (pow_nonneg hq0.le s)
      (hqs.trans hq1.le) hq0.le hq1.le n).2
