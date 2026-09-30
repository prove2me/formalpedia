-- Prove2me | solution 1 for lean_workbook_plus_26296
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:25:39.80555+00:00
-- url     : https://prove2.me/submissions/926a8823-20b8-4154-bb6a-824bc1eee4a4

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

noncomputable def mobiusTail (c : ℝ) (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + c)

theorem mobius_tail_gt_one (c : ℝ) (hc : 0 < c) (n : ℕ) : 1 < mobiusTail c n := by
  dsimp [mobiusTail]
  have hd : 0 < (n : ℝ) + c := by positivity
  linarith [one_div_pos.mpr hd]

theorem mobius_tail_recurrence (c : ℝ) (hc : 0 < c) (n : ℕ) :
    mobiusTail c (n + 1) = 2 - 1 / mobiusTail c n := by
  have hd : 0 < (n : ℝ) + c := by positivity
  have hd1 : 0 < (n : ℝ) + c + 1 := by positivity
  have heq : mobiusTail c n = ((n : ℝ) + c + 1) / ((n : ℝ) + c) := by
    unfold mobiusTail
    field_simp
  rw [heq, one_div_div]
  unfold mobiusTail
  push_cast
  have hrearrange : (n : ℝ) + 1 + c = (n : ℝ) + c + 1 := by ring
  rw [hrearrange]
  field_simp
  ring

theorem mobius_tail_strictAnti (c : ℝ) (hc : 0 < c) : StrictAnti (mobiusTail c) := by
  intro n m hnm
  have hd : 0 < (n : ℝ) + c := by positivity
  have hlt : (n : ℝ) + c < (m : ℝ) + c := by
    have hn : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  simpa only [mobiusTail, add_comm] using add_lt_add_left (one_div_lt_one_div_of_lt hd hlt) 1

theorem mobius_tail_tendsto (c : ℝ) : Tendsto (mobiusTail c) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
  unfold mobiusTail
  simpa only [one_div, Pi.inv_apply, add_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).add hden.inv_tendsto_atTop

theorem mobius_tail_scaled_error (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * (mobiusTail c n - 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 1 - c / ((n : ℝ) + c)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := c)).mul hden.inv_tendsto_atTop)
  apply hlim.congr'
  filter_upwards with n
  have hd : 0 < (n : ℝ) + c := by positivity
  unfold mobiusTail
  field_simp
  ring

theorem mobius_recurrence_tail_formula (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) (n : ℕ) :
    x (n + 1) = mobiusTail (1 / (x 1 - 1)) n := by
  have hc : 0 < 1 / (x 1 - 1) := one_div_pos.mpr (sub_pos.mpr h)
  induction n with
  | zero => simp [mobiusTail]
  | succ n ih =>
    rw [hx (n + 1), ih, mobius_tail_recurrence _ hc]

theorem mobius_recurrence_conjugacy (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) (n : ℕ) :
    1 / (x (n + 1) - 1) = (n : ℝ) + 1 / (x 1 - 1) := by
  rw [mobius_recurrence_tail_formula x hx h n]
  simp [mobiusTail]

theorem mobius_recurrence_closed_form (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) (n : ℕ) :
    x (n + 1) = 1 + (x 1 - 1) / (1 + (n : ℝ) * (x 1 - 1)) := by
  rw [mobius_recurrence_tail_formula x hx h n]
  have hd : 0 < x 1 - 1 := by linarith
  have hn : 0 < (n : ℝ) + 1 / (x 1 - 1) := by positivity
  have hn' : 0 < 1 + (n : ℝ) * (x 1 - 1) := by positivity
  unfold mobiusTail
  field_simp
  ring

theorem mobius_recurrence_positive_strictAnti (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) :
    (∀ n, 1 < x (n + 1)) ∧ StrictAnti (fun n => x (n + 1)) := by
  have hc : 0 < 1 / (x 1 - 1) := one_div_pos.mpr (sub_pos.mpr h)
  have heq : (fun n => x (n + 1)) = mobiusTail (1 / (x 1 - 1)) :=
    funext (mobius_recurrence_tail_formula x hx h)
  constructor
  · intro n
    rw [mobius_recurrence_tail_formula x hx h n]
    exact mobius_tail_gt_one _ hc n
  · rw [heq]
    exact mobius_tail_strictAnti _ hc

theorem mobius_recurrence_limit (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) :
    Tendsto x atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have heq : (fun n => x (n + 1)) = mobiusTail (1 / (x 1 - 1)) :=
    funext (mobius_recurrence_tail_formula x hx h)
  rw [heq]
  exact mobius_tail_tendsto _

theorem mobius_recurrence_scaled_error (x : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = 2 - 1 / x n) (h : 1 < x 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (x (n + 1) - 1)) atTop (𝓝 1) := by
  have hc : 0 < 1 / (x 1 - 1) := one_div_pos.mpr (sub_pos.mpr h)
  apply (mobius_tail_scaled_error (1 / (x 1 - 1)) hc).congr'
  filter_upwards with n
  rw [mobius_recurrence_tail_formula x hx h n]

theorem solution (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = 2 - 1 / x n)
    (h : x 1 > 1) : x 1 > x 2 := by
  simpa only [Nat.zero_add] using
    (mobius_recurrence_positive_strictAnti x hx h).2 (show (0 : ℕ) < 1 by decide)

#print axioms mobiusTail
#print axioms mobius_tail_gt_one
#print axioms mobius_tail_recurrence
#print axioms mobius_tail_strictAnti
#print axioms mobius_tail_tendsto
#print axioms mobius_tail_scaled_error
#print axioms mobius_recurrence_tail_formula
#print axioms mobius_recurrence_conjugacy
#print axioms mobius_recurrence_closed_form
#print axioms mobius_recurrence_positive_strictAnti
#print axioms mobius_recurrence_limit
#print axioms mobius_recurrence_scaled_error
#print axioms solution
