-- Prove2me | solution 1 for lean_workbook_plus_43357
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:54:07.737296+00:00
-- url     : https://prove2.me/submissions/683993f8-6253-4f33-958a-7d5961c9f51d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem weighted_decay_ratio_range (a : ℝ) (ha : 0 < a) :
    0 < 2 * a / (1 + 2 * a) ∧ 2 * a / (1 + 2 * a) < 1 := by
  have hd : 0 < 1 + 2 * a := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩

theorem weighted_decay_step_bound (a n t : ℝ) (ha : 0 < a) (hn : 1 ≤ n)
    (ht : 0 < t) (hnt : n * t ≤ a) :
    (n + 1) * (n * t ^ 2 / (1 + (n + 1) * t)) ≤
      (n * t) * (2 * a / (1 + 2 * a)) := by
  have hd : 0 < 1 + (n + 1) * t := by positivity
  have ha' : 0 < 1 + 2 * a := by linarith
  have hs : (n + 1) * t ≤ 2 * a := by nlinarith [mul_nonneg (by linarith : 0 ≤ n - 1) ht.le]
  have hr : (n + 1) * t / (1 + (n + 1) * t) ≤ 2 * a / (1 + 2 * a) := by
    apply (div_le_div_iff₀ hd ha').mpr
    nlinarith
  calc
    (n + 1) * (n * t ^ 2 / (1 + (n + 1) * t)) =
        (n * t) * ((n + 1) * t / (1 + (n + 1) * t)) := by ring
    _ ≤ (n * t) * (2 * a / (1 + 2 * a)) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (by linarith) ht.le)

theorem weighted_decay_invariants (v : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hv : v 0 = a)
    (hrec : ∀ n, v (n + 1) = ((n : ℝ) + 1) * v n ^ 2 / (1 + ((n : ℝ) + 2) * v n))
    (n : ℕ) : 0 < v n ∧ ((n : ℝ) + 1) * v n ≤ a * (2 * a / (1 + 2 * a)) ^ n := by
  have hr := weighted_decay_ratio_range a ha
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one, hv] using And.intro ha (le_refl a)
  | succ n ih =>
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hb : ((n : ℝ) + 1) * v n ≤ a :=
      ih.2.trans (by nlinarith [pow_le_one₀ hr.1.le hr.2.le (n := n)])
    have hs := weighted_decay_step_bound a ((n : ℝ) + 1) (v n) ha hn ih.1 hb
    have hvn : 0 < v n := ih.1
    have hp : 0 < v (n + 1) := by rw [hrec]; positivity
    refine ⟨hp, ?_⟩
    rw [hrec]
    push_cast
    calc
      ((n : ℝ) + 1 + 1) * (((n : ℝ) + 1) * v n ^ 2 / (1 + ((n : ℝ) + 2) * v n))
          ≤ (((n : ℝ) + 1) * v n) * (2 * a / (1 + 2 * a)) := by
            convert hs using 1 <;> congr 1 <;> ring
      _ ≤ (a * (2 * a / (1 + 2 * a)) ^ n) * (2 * a / (1 + 2 * a)) :=
        mul_le_mul_of_nonneg_right ih.2 hr.1.le
      _ = a * (2 * a / (1 + 2 * a)) ^ (n + 1) := by rw [pow_succ]; ring

theorem weighted_decay_strictAnti (v : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hv : v 0 = a)
    (hrec : ∀ n, v (n + 1) = ((n : ℝ) + 1) * v n ^ 2 / (1 + ((n : ℝ) + 2) * v n)) :
    StrictAnti v := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hp := (weighted_decay_invariants v a ha hv hrec n).1
  have hd : 0 < 1 + ((n : ℝ) + 2) * v n := by positivity
  rw [hrec]
  apply (div_lt_iff₀ hd).mpr
  nlinarith [sq_nonneg (v n)]

theorem weighted_decay_weighted_tendsto_zero (v : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hv : v 0 = a)
    (hrec : ∀ n, v (n + 1) = ((n : ℝ) + 1) * v n ^ 2 / (1 + ((n : ℝ) + 2) * v n)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * v n) atTop (𝓝 0) := by
  have hr := weighted_decay_ratio_range a ha
  have ht : Tendsto (fun n : ℕ => a * (2 * a / (1 + 2 * a)) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2).const_mul a
  apply squeeze_zero _ (fun n => (weighted_decay_invariants v a ha hv hrec n).2) ht
  intro n
  exact mul_nonneg (by positivity) (weighted_decay_invariants v a ha hv hrec n).1.le

theorem weighted_decay_tendsto_zero (v : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hv : v 0 = a)
    (hrec : ∀ n, v (n + 1) = ((n : ℝ) + 1) * v n ^ 2 / (1 + ((n : ℝ) + 2) * v n)) :
    Tendsto v atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (weighted_decay_invariants v a ha hv hrec n).1.le) _
    (weighted_decay_weighted_tendsto_zero v a ha hv hrec)
  intro n
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (weighted_decay_invariants v a ha hv hrec n).1.le]

theorem source_weighted_recurrence_shift (x : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n)) :
    ∀ n, (fun k => x (k + 1)) (n + 1) =
      ((n : ℝ) + 1) * (fun k => x (k + 1)) n ^ 2 /
        (1 + ((n : ℝ) + 2) * (fun k => x (k + 1)) n) := by
  intro n
  have h := hrec (n + 1) (Nat.succ_pos n)
  simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using h

theorem source_weighted_recurrence_rate (x : ℕ → ℝ) (hx : 0 < x 1)
    (hrec : ∀ n, 0 < n → x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n))
    (n : ℕ) : 0 < x (n + 1) ∧
      ((n : ℝ) + 1) * x (n + 1) ≤ x 1 * (2 * x 1 / (1 + 2 * x 1)) ^ n :=
  weighted_decay_invariants (fun n => x (n + 1)) (x 1) hx rfl (source_weighted_recurrence_shift x hrec) n

theorem source_weighted_recurrence_strictAnti (x : ℕ → ℝ) (hx : 0 < x 1)
    (hrec : ∀ n, 0 < n → x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n)) :
    StrictAnti (fun n => x (n + 1)) :=
  weighted_decay_strictAnti (fun n => x (n + 1)) (x 1) hx rfl (source_weighted_recurrence_shift x hrec)

theorem source_weighted_recurrence_tendsto (x : ℕ → ℝ) (hx : 0 < x 1)
    (hrec : ∀ n, 0 < n → x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n)) :
    Tendsto (fun n : ℕ => (n : ℝ) * x n) atTop (𝓝 0) := by
  have ht := weighted_decay_weighted_tendsto_zero (fun n => x (n + 1)) (x 1) hx rfl
    (source_weighted_recurrence_shift x hrec)
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem source_half_initial_rate (x : ℕ → ℝ) (hx : x 1 = 1 / 2)
    (hrec : ∀ n, 0 < n → x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n))
    (n : ℕ) : 0 < x (n + 1) ∧ ((n : ℝ) + 1) * x (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have hp : 0 < x 1 := by rw [hx]; norm_num
  have h := source_weighted_recurrence_rate x hp hrec n
  rw [hx] at h
  rw [show 2 * (1 / 2 : ℝ) / (1 + 2 * (1 / 2 : ℝ)) = 1 / 2 by ring] at h
  simpa only [pow_succ', one_div] using h

theorem weighted_recurrence_zero_index (x : ℕ → ℝ)
    (hrec : ∀ n, x (n + 1) = (n : ℝ) * x n ^ 2 / (1 + ((n : ℝ) + 1) * x n)) : x 1 = 0 := by
  simpa only [Nat.cast_zero, zero_add, zero_mul, zero_div] using hrec 0

theorem solution (x : ℕ → ℝ)
    (hx : x 1 = 1 / 2 ∧ ∀ n, x (n + 1) = n * x n ^ 2 / (1 + (n + 1) * x n)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |n * x n| < ε := by
  have hp : 0 < x 1 := by rw [hx.1]; norm_num
  have ht := source_weighted_recurrence_tendsto x hp (fun n _ => hx.2 n)
  intro ε hε
  have ha : Tendsto (fun n : ℕ => |(n : ℝ) * x n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using ht.norm
  exact eventually_atTop.mp (ha.eventually (gt_mem_nhds hε))

#print axioms weighted_decay_ratio_range
#print axioms weighted_decay_step_bound
#print axioms weighted_decay_invariants
#print axioms weighted_decay_strictAnti
#print axioms weighted_decay_weighted_tendsto_zero
#print axioms weighted_decay_tendsto_zero
#print axioms source_weighted_recurrence_shift
#print axioms source_weighted_recurrence_rate
#print axioms source_weighted_recurrence_strictAnti
#print axioms source_weighted_recurrence_tendsto
#print axioms source_half_initial_rate
#print axioms weighted_recurrence_zero_index
#print axioms solution
