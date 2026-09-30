-- Prove2me | solution 1 for lean_workbook_plus_37925
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:16:46.280055+00:00
-- url     : https://prove2.me/submissions/07fbd5e0-d3cb-47f7-a46e-c9ceca799431

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem finite_euler_positive (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (k : ℕ) (hk : k ≤ n) : 0 < a k := by
  induction k with
  | zero => rw [h0]; norm_num
  | succ k ih =>
    rw [hr k (by omega)]
    have hp := ih (by omega)
    positivity

theorem euler_reciprocal_step (N z : ℝ) (hN : 0 < N) (hz : 0 < z) :
    1 / (z + z ^ 2 / N) = 1 / z - 1 / (N + z) := by
  have hs : z + z ^ 2 / N ≠ 0 := by positivity
  have hd : N + z ≠ 0 := by positivity
  field_simp
  ring

theorem finite_euler_reciprocal_lower (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (k : ℕ) (hk : k ≤ n) :
    2 - (k : ℝ) / n ≤ 1 / a k ∧ (0 < k → 2 - (k : ℝ) / n < 1 / a k) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hp := finite_euler_positive n hn a h0 hr k (by omega)
    have he : 1 / a (k + 1) = 1 / a k - 1 / ((n : ℝ) + a k) := by
      rw [hr k (by omega)]
      exact euler_reciprocal_step n (a k) hnR hp
    have hd := one_div_lt_one_div_of_lt hnR (show (n : ℝ) < n + a k by linarith)
    have hi := (ih (by omega)).1
    have ht : 2 - ((k + 1 : ℕ) : ℝ) / n < 1 / a (k + 1) := by
      rw [Nat.cast_add, Nat.cast_one, add_div]
      linarith
    exact ⟨ht.le, fun _ => ht⟩

theorem finite_euler_lt_one (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (k : ℕ) (hk : k ≤ n) : a k < 1 := by
  by_cases hk0 : k = 0
  · subst k; rw [h0]; norm_num
  have hp := finite_euler_positive n hn a h0 hr k hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkn : (k : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hk)
  have hb := (finite_euler_reciprocal_lower n hn a h0 hr k hk).2 (by omega)
  have hi : 1 < 1 / a k := by linarith
  simpa only [one_mul] using (lt_div_iff₀ hp).mp hi

theorem finite_euler_reciprocal_upper (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (k : ℕ) (hk : k ≤ n) :
    1 / a k ≤ 2 - (k : ℝ) / (n + 1) ∧
      (0 < k → 1 / a k < 2 - (k : ℝ) / (n + 1)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hp := finite_euler_positive n hn a h0 hr k (by omega)
    have hu := finite_euler_lt_one n hn a h0 hr k (by omega)
    have he : 1 / a (k + 1) = 1 / a k - 1 / ((n : ℝ) + a k) := by
      rw [hr k (by omega)]
      exact euler_reciprocal_step n (a k) hnR hp
    have hd := one_div_lt_one_div_of_lt (show 0 < (n : ℝ) + a k by linarith)
      (show (n : ℝ) + a k < n + 1 by linarith)
    have hi := (ih (by omega)).1
    have ht : 1 / a (k + 1) < 2 - ((k + 1 : ℕ) : ℝ) / (n + 1) := by
      rw [Nat.cast_add, Nat.cast_one, add_div]
      linarith
    exact ⟨ht.le, fun _ => ht⟩

theorem finite_euler_terminal_strong_bounds (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n) :
    ((n : ℝ) + 1) / (n + 2) < a n ∧ a n < 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp := finite_euler_positive n hn a h0 hr n le_rfl
  have hb := (finite_euler_reciprocal_upper n hn a h0 hr n le_rfl).2 hn
  have he : 2 - (n : ℝ) / (n + 1) = (n + 2) / (n + 1) := by field_simp; ring
  rw [he] at hb
  have ht := (div_lt_div_iff₀ hp (show 0 < (n : ℝ) + 1 by linarith)).mp hb
  refine ⟨(div_lt_iff₀ (show 0 < (n : ℝ) + 2 by linarith)).mpr ?_,
    finite_euler_lt_one n hn a h0 hr n le_rfl⟩
  nlinarith

theorem finite_euler_source_bounds (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n) :
    1 - 1 / (n : ℝ) < a n ∧ a n < 1 := by
  have hs := finite_euler_terminal_strong_bounds n hn a h0 hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi := one_div_lt_one_div_of_lt hnR (show (n : ℝ) < n + 2 by linarith)
  have he : 1 - 1 / ((n : ℝ) + 2) = (n + 1) / (n + 2) := by field_simp; ring
  exact ⟨(show 1 - 1 / (n : ℝ) < (n + 1) / (n + 2) by rw [← he]; linarith).trans hs.1, hs.2⟩

theorem finite_euler_step_strict (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (k : ℕ) (hk : k < n) : a k < a (k + 1) := by
  have hp := finite_euler_positive n hn a h0 hr k hk.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [hr k hk]
  have hd : 0 < (a k) ^ 2 / n := div_pos (sq_pos_of_pos hp) hnR
  linarith

theorem finite_euler_terminal_error (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (h0 : a 0 = 1 / 2) (hr : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n) :
    0 < 1 - a n ∧ 1 - a n < 1 / ((n : ℝ) + 2) := by
  have hs := finite_euler_terminal_strong_bounds n hn a h0 hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : 1 - 1 / ((n : ℝ) + 2) = (n + 1) / (n + 2) := by field_simp; ring
  constructor <;> linarith

theorem finite_euler_family_terminal_tendsto (a : ℕ → ℕ → ℝ)
    (h0 : ∀ n > 0, a n 0 = 1 / 2)
    (hr : ∀ n > 0, ∀ k < n, a n (k + 1) = a n k + (a n k) ^ 2 / n) :
    Tendsto (fun n : ℕ => a n n) atTop (𝓝 1) := by
  have hl : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (finite_euler_source_bounds n hn (a n) (h0 n hn) (hr n hn)).1.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (finite_euler_source_bounds n hn (a n) (h0 n hn) (hr n hn)).2.le

noncomputable def finiteEulerOrbit (n : ℕ) : ℕ → ℝ :=
  Nat.rec (1 / 2) (fun _ z => z + z ^ 2 / n)

theorem finite_euler_orbit_zero (n : ℕ) : finiteEulerOrbit n 0 = 1 / 2 := rfl

theorem finite_euler_orbit_succ (n k : ℕ) :
    finiteEulerOrbit n (k + 1) = finiteEulerOrbit n k + (finiteEulerOrbit n k) ^ 2 / n := rfl

theorem finite_euler_orbit_terminal_tendsto :
    Tendsto (fun n : ℕ => finiteEulerOrbit n n) atTop (𝓝 1) := by
  apply finite_euler_family_terminal_tendsto
  · exact fun n _ => finite_euler_orbit_zero n
  · exact fun n _ k _ => finite_euler_orbit_succ n k

theorem finite_euler_unique_prefix (n : ℕ) (a b : ℕ → ℝ) (h0 : a 0 = b 0)
    (ha : ∀ k < n, a (k + 1) = a k + (a k) ^ 2 / n)
    (hb : ∀ k < n, b (k + 1) = b k + (b k) ^ 2 / n)
    (k : ℕ) (hk : k ≤ n) : a k = b k := by
  induction k with
  | zero => exact h0
  | succ k ih => rw [ha k (by omega), hb k (by omega), ih (by omega)]

theorem solution (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 = 1 / 2)
    (ha' : ∀ k, a k = a (k - 1) + (a (k - 1)) ^ 2 / n) :
    1 - 1 / (n : ℝ) < a n ∧ a n < 1 := by
  apply finite_euler_source_bounds n hn a ha
  intro k hk
  simpa only [Nat.add_sub_cancel] using ha' (k + 1)

#print axioms finite_euler_positive
#print axioms euler_reciprocal_step
#print axioms finite_euler_reciprocal_lower
#print axioms finite_euler_lt_one
#print axioms finite_euler_reciprocal_upper
#print axioms finite_euler_terminal_strong_bounds
#print axioms finite_euler_source_bounds
#print axioms finite_euler_step_strict
#print axioms finite_euler_terminal_error
#print axioms finite_euler_family_terminal_tendsto
#print axioms finiteEulerOrbit
#print axioms finite_euler_orbit_zero
#print axioms finite_euler_orbit_succ
#print axioms finite_euler_orbit_terminal_tendsto
#print axioms finite_euler_unique_prefix
#print axioms solution
