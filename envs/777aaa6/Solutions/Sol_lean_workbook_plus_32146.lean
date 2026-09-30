-- Prove2me | solution 1 for lean_workbook_plus_32146
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:29:35.622901+00:00
-- url     : https://prove2.me/submissions/9f71ff5f-d487-4059-bc04-1651d5c59699

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem logistic_update_bounds (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    0 < t - t ^ 2 ∧ t - t ^ 2 < t ∧ t - t ^ 2 ≤ 1 / 2 := by
  have hpos : 0 < t * (1 - t) := mul_pos ht (by linarith)
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem logistic_recurrence_bounds (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) :
    ∀ n, 0 < x n ∧ x n ≤ 1 / 2 := by
  intro n
  induction n with
  | zero => rw [hzero]; norm_num
  | succ n ih =>
    rw [hrec]
    exact ⟨(logistic_update_bounds _ ih.1 ih.2).1,
      (logistic_update_bounds _ ih.1 ih.2).2.2⟩

theorem logistic_recurrence_strictAnti (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) : StrictAnti x := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [hrec]
  exact (logistic_update_bounds _ (logistic_recurrence_bounds x hzero hrec n).1
    (logistic_recurrence_bounds x hzero hrec n).2).2.1

theorem logistic_reciprocal_increment (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) (n : ℕ) :
    1 / x (n + 1) = 1 / x n + 1 / (1 - x n) := by
  have hx := logistic_recurrence_bounds x hzero hrec n
  have hd : 0 < 1 - x n := by linarith [hx.2]
  have heq : x (n + 1) = x n * (1 - x n) := by rw [hrec]; ring
  rw [heq]
  field_simp [ne_of_gt hx.1, ne_of_gt hd] <;> ring

theorem logistic_reciprocal_bounds (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) (n : ℕ) :
    (n : ℝ) + 2 ≤ 1 / x n ∧ 1 / x n ≤ 2 * (n : ℝ) + 2 := by
  induction n with
  | zero => rw [hzero]; norm_num
  | succ n ih =>
    have hx := logistic_recurrence_bounds x hzero hrec n
    have hd : 0 < 1 - x n := by linarith [hx.2]
    have hstep : 1 ≤ 1 / (1 - x n) ∧ 1 / (1 - x n) ≤ 2 := by
      constructor
      · apply (le_div_iff₀ hd).mpr
        linarith [hx.1]
      · apply (div_le_iff₀ hd).mpr
        linarith [hx.2]
    rw [logistic_reciprocal_increment x hzero hrec n]
    push_cast
    constructor <;> linarith [ih.1, ih.2, hstep.1, hstep.2]

theorem logistic_harmonic_bounds (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) (n : ℕ) :
    1 / (2 * (n : ℝ) + 2) ≤ x n ∧ x n ≤ 1 / ((n : ℝ) + 2) := by
  have hx := (logistic_recurrence_bounds x hzero hrec n).1
  have hi := logistic_reciprocal_bounds x hzero hrec n
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 2)).mpr
    have h := (div_le_iff₀ hx).mp hi.2
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 2)).mpr
    have h := (le_div_iff₀ hx).mp hi.1
    nlinarith

theorem logistic_recurrence_tendsto_zero (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) : Tendsto x atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [one_div] using hden.inv_tendsto_atTop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (logistic_recurrence_bounds x hzero hrec n).1.le)
    (fun n => (logistic_harmonic_bounds x hzero hrec n).2)

theorem logistic_recurrence_not_summable (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) : ¬ Summable x := by
  intro hs
  have hsmall : Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 2)) :=
    hs.of_nonneg_of_le (fun n => by positivity)
      (fun n => (logistic_harmonic_bounds x hzero hrec n).1)
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply (hsmall.mul_left 2).congr
    intro n
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hd' : 0 < 2 * (n : ℝ) + 2 := by positivity
    field_simp
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem logistic_square_partial_sum (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) (N : ℕ) :
    ∑ n ∈ Finset.range N, (x n) ^ 2 = 1 / 2 - x N := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hrec]
    ring

theorem logistic_square_hasSum (x : ℕ → ℝ) (hzero : x 0 = 1 / 2)
    (hrec : ∀ n, x (n + 1) = x n - (x n) ^ 2) :
    HasSum (fun n => (x n) ^ 2) (1 / 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg (x n)) _).mpr
  have hlim : Tendsto (fun N => 1 / 2 - x N) atTop (𝓝 (1 / 2)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
        (logistic_recurrence_tendsto_zero x hzero hrec)
  apply hlim.congr'
  filter_upwards with N
  exact (logistic_square_partial_sum x hzero hrec N).symm

noncomputable def logisticDecay : ℕ → ℝ :=
  Nat.rec (1 / 2) (fun _ t => t - t ^ 2)

theorem logistic_decay_zero : logisticDecay 0 = 1 / 2 := rfl

theorem logistic_decay_recurrence (n : ℕ) :
    logisticDecay (n + 1) = logisticDecay n - (logisticDecay n) ^ 2 := rfl

theorem logistic_decay_full_dynamics :
    StrictAnti logisticDecay ∧ Tendsto logisticDecay atTop (𝓝 0) ∧
      ¬ Summable logisticDecay ∧ HasSum (fun n => (logisticDecay n) ^ 2) (1 / 2) := by
  exact ⟨logistic_recurrence_strictAnti _ logistic_decay_zero logistic_decay_recurrence,
    logistic_recurrence_tendsto_zero _ logistic_decay_zero logistic_decay_recurrence,
    logistic_recurrence_not_summable _ logistic_decay_zero logistic_decay_recurrence,
    logistic_square_hasSum _ logistic_decay_zero logistic_decay_recurrence⟩

theorem logistic_source_positive_index_counterexample :
    ∃ x : ℕ → ℝ, x 1 = 1 / 2 ∧
      (∀ n, 0 < n → x (n + 1) = x n - (x n) ^ 2) ∧
      ¬ Summable (fun n => x (n + 1)) ∧
      HasSum (fun n => (x (n + 1)) ^ 2) (1 / 2) := by
  refine ⟨fun n => logisticDecay (n - 1), ?_, ?_, ?_, ?_⟩
  · exact logistic_decay_zero
  · intro n hn
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa only [Nat.add_sub_cancel, hn'] using logistic_decay_recurrence (n - 1)
  · simpa only [Nat.add_sub_cancel] using logistic_decay_full_dynamics.2.2.1
  · simpa only [Nat.add_sub_cancel] using logistic_decay_full_dynamics.2.2.2

theorem solution (x : ℕ → ℝ)
    (hx : x 1 = 1 / 2 ∧ ∀ n, x (n + 1) = x n - (x n) ^ 2) : Summable x := by
  have hrec := hx.2 0
  have hzero := hx.1
  norm_num only [Nat.zero_add] at hrec
  nlinarith [sq_nonneg (x 0 - 1 / 2)]

#print axioms logistic_update_bounds
#print axioms logistic_recurrence_bounds
#print axioms logistic_recurrence_strictAnti
#print axioms logistic_reciprocal_increment
#print axioms logistic_reciprocal_bounds
#print axioms logistic_harmonic_bounds
#print axioms logistic_recurrence_tendsto_zero
#print axioms logistic_recurrence_not_summable
#print axioms logistic_square_partial_sum
#print axioms logistic_square_hasSum
#print axioms logisticDecay
#print axioms logistic_decay_zero
#print axioms logistic_decay_recurrence
#print axioms logistic_decay_full_dynamics
#print axioms logistic_source_positive_index_counterexample
#print axioms solution
