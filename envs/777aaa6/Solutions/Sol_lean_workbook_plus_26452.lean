-- Prove2me | solution 1 for lean_workbook_plus_26452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:48:09.899278+00:00
-- url     : https://prove2.me/submissions/285ae31c-3a16-467e-906b-14ec352aadcb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem quadratic_iteration_nonneg (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (n : ℕ) : 0 ≤ u n := by
  cases n with
  | zero => exact h0
  | succ n => rw [hrec]; positivity

theorem quadratic_iteration_strictMono_of_step (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (hstep : u 0 < u 1) :
    StrictMono u := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n with
  | zero => exact hstep
  | succ n ih =>
    have hn := quadratic_iteration_nonneg u h0 hrec n
    have hp : 0 < (u (n + 1) - u n) * (u (n + 1) + u n) :=
      mul_pos (sub_pos.mpr ih) (by linarith)
    nlinarith [hrec (n + 1), hrec n]

theorem quadratic_iteration_strictAnti_of_step (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (hstep : u 1 < u 0) :
    StrictAnti u := by
  apply strictAnti_nat_of_succ_lt
  intro n
  induction n with
  | zero => exact hstep
  | succ n ih =>
    have hn := quadratic_iteration_nonneg u h0 hrec (n + 1)
    have hp : 0 < (u n - u (n + 1)) * (u n + u (n + 1)) :=
      mul_pos (sub_pos.mpr ih) (by linarith)
    nlinarith [hrec (n + 1), hrec n]

theorem quadratic_iteration_below_one_increasing (u : ℕ → ℝ)
    (h0 : 0 ≤ u 0) (h1 : u 0 < 1)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : StrictMono u := by
  apply quadratic_iteration_strictMono_of_step u h0 hrec
  rw [hrec 0]
  have hp : 0 < (1 - u 0) * (2 - u 0) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem quadratic_iteration_between_fixed_points_decreasing (u : ℕ → ℝ)
    (h1 : 1 < u 0) (h2 : u 0 < 2)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : StrictAnti u := by
  apply quadratic_iteration_strictAnti_of_step u (by linarith) hrec
  rw [hrec 0]
  have hp : 0 < (u 0 - 1) * (2 - u 0) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem quadratic_iteration_above_two_increasing (u : ℕ → ℝ) (h2 : 2 < u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : StrictMono u := by
  apply quadratic_iteration_strictMono_of_step u (by linarith) hrec
  rw [hrec 0]
  have hp : 0 < (u 0 - 1) * (u 0 - 2) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem quadratic_iteration_fixed (u : ℕ → ℝ) (c : ℝ) (h0 : u 0 = c)
    (hc : c = 1 ∨ c = 2)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : ∀ n, u n = c := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hrec, ih]; rcases hc with rfl | rfl <;> norm_num

theorem quadratic_iteration_invariant_interval (u : ℕ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hM2 : M ≤ 2) (h0 : 0 ≤ u 0) (h0M : u 0 ≤ M)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (n : ℕ) :
    0 ≤ u n ∧ u n ≤ M := by
  induction n with
  | zero => exact ⟨h0, h0M⟩
  | succ n ih =>
    rw [hrec]
    refine ⟨by positivity, ?_⟩
    have hsq : 0 ≤ (M - u n) * (M + u n) := mul_nonneg (by linarith [ih.2]) (by linarith [ih.1])
    have hm : 0 ≤ (M - 1) * (2 - M) := mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem quadratic_iteration_geometric_error (u : ℕ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hM2 : M ≤ 2) (h0 : 0 ≤ u 0) (h0M : u 0 ≤ M)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (n : ℕ) :
    |u n - 1| ≤ |u 0 - 1| * ((M + 1) / 3) ^ n := by
  have hr : 0 ≤ (M + 1) / 3 := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := quadratic_iteration_invariant_interval u M hM hM2 h0 h0M hrec n
    have hid : u (n + 1) - 1 = (u n - 1) * ((u n + 1) / 3) := by rw [hrec]; ring
    have hn' : 0 ≤ (u n + 1) / 3 := by linarith [hn.1]
    rw [hid, abs_mul, abs_of_nonneg hn']
    calc
      |u n - 1| * ((u n + 1) / 3) ≤ |u n - 1| * ((M + 1) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith [hn.2]) (abs_nonneg _)
      _ ≤ (|u 0 - 1| * ((M + 1) / 3) ^ n) * ((M + 1) / 3) :=
        mul_le_mul_of_nonneg_right ih hr
      _ = |u 0 - 1| * ((M + 1) / 3) ^ (n + 1) := by rw [pow_succ]; ring

theorem quadratic_iteration_tendsto_one (u : ℕ → ℝ) (h0 : 0 ≤ u 0) (h2 : u 0 < 2)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : Tendsto u atTop (𝓝 1) := by
  let M := max (u 0) 1
  have hM : 1 ≤ M := le_max_right _ _
  have hM2 : M < 2 := max_lt h2 (by norm_num)
  have h0M : u 0 ≤ M := le_max_left _ _
  have hr : 0 ≤ (M + 1) / 3 := by linarith
  have hr1 : (M + 1) / 3 < 1 := by linarith
  have ht : Tendsto (fun n : ℕ => |u 0 - 1| * ((M + 1) / 3) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul |u 0 - 1|
  have he : Tendsto (fun n => |u n - 1|) atTop (𝓝 0) := squeeze_zero
    (fun n => abs_nonneg (u n - 1))
    (quadratic_iteration_geometric_error u M hM hM2.le h0 h0M hrec) ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)

theorem quadratic_iteration_linear_growth (u : ℕ → ℝ) (h2 : 2 < u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) (n : ℕ) :
    u 0 + (n : ℝ) * ((u 0 - 1) * (u 0 - 2) / 3) ≤ u n := by
  have hm := (quadratic_iteration_above_two_increasing u h2 hrec).monotone
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : u 0 ≤ u n := hm (Nat.zero_le n)
    have hp : 0 ≤ (u n - u 0) * (u n + u 0 - 3) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hrec]
    push_cast
    nlinarith

theorem quadratic_iteration_tendsto_atTop (u : ℕ → ℝ) (h2 : 2 < u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) : Tendsto u atTop atTop := by
  let d := (u 0 - 1) * (u 0 - 2) / 3
  have hd : 0 < d := div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  apply tendsto_atTop.mpr
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt ((R - u 0) / d)
  have hN' : R - u 0 < (N : ℝ) * d := (div_lt_iff₀ hd).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hg : u 0 + (n : ℝ) * d ≤ u n := quadratic_iteration_linear_growth u h2 hrec n
  nlinarith

theorem quadratic_iteration_finite_limit_iff (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = ((u n) ^ 2 + 2) / 3) :
    (∃ L : ℝ, Tendsto u atTop (𝓝 L)) ↔ u 0 ≤ 2 := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra! h2
    exact not_tendsto_nhds_of_tendsto_atTop (quadratic_iteration_tendsto_atTop u h2 hrec) L hL
  · intro h2
    rcases h2.eq_or_lt with heq | hlt
    · have hu := quadratic_iteration_fixed u 2 heq (Or.inr rfl) hrec
      refine ⟨2, ?_⟩
      have heq : u = fun _ => (2 : ℝ) := funext hu
      rw [heq]
      exact tendsto_const_nhds
    · exact ⟨1, quadratic_iteration_tendsto_one u h0 hlt hrec⟩

theorem source_quadratic_monotonicity (x : ℕ → ℝ) (hx : 0 < x 1)
    (hrec : ∀ n, 0 < n → x (n + 1) = ((x n) ^ 2 + 2) / 3) :
    (x 1 < x 2 → StrictMono (fun n => x (n + 1))) ∧
      (x 2 < x 1 → StrictAnti (fun n => x (n + 1))) := by
  have hr : ∀ n, (fun k => x (k + 1)) (n + 1) =
      (((fun k => x (k + 1)) n) ^ 2 + 2) / 3 := fun n => hrec (n + 1) (Nat.succ_pos n)
  exact ⟨fun h => quadratic_iteration_strictMono_of_step (fun n => x (n + 1)) hx.le hr h,
    fun h => quadratic_iteration_strictAnti_of_step (fun n => x (n + 1)) hx.le hr h⟩

theorem source_quadratic_dynamics (x : ℕ → ℝ) (hx : 0 < x 1)
    (hrec : ∀ n, 0 < n → x (n + 1) = ((x n) ^ 2 + 2) / 3) :
    (x 1 < 2 → Tendsto x atTop (𝓝 1)) ∧
      (x 1 = 2 → ∀ n, 0 < n → x n = 2) ∧
      (2 < x 1 → Tendsto x atTop atTop) := by
  have hr : ∀ n, (fun k => x (k + 1)) (n + 1) =
      (((fun k => x (k + 1)) n) ^ 2 + 2) / 3 := fun n => hrec (n + 1) (Nat.succ_pos n)
  refine ⟨fun h => (tendsto_add_atTop_iff_nat 1).mp
    (quadratic_iteration_tendsto_one (fun n => x (n + 1)) hx.le h hr), ?_,
    fun h => (tendsto_add_atTop_iff_nat 1).mp
      (quadratic_iteration_tendsto_atTop (fun n => x (n + 1)) h hr)⟩
  intro h n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact quadratic_iteration_fixed (fun n => x (n + 1)) 2 h (Or.inr rfl) hr k

theorem posted_quadratic_strict_growth (x : ℕ → ℝ)
    (hrec : ∀ n, x (n + 1) = (x n) ^ 2 + 2 / 3) (n : ℕ) : x n < x (n + 1) := by
  rw [hrec]
  nlinarith [sq_nonneg (x n - 1 / 2)]

theorem solution (a : ℝ) (x : ℕ → ℝ) (hx : x 1 = a)
    (hn : ∀ n : ℕ, x (n + 1) = (x n) ^ 2 + 2 / 3) :
    (x 2 > x 1 → ∀ n : ℕ, x (n + 1) > x n) ∧
      (x 2 < x 1 → ∀ n : ℕ, x (n + 1) < x n) := by
  constructor
  · intro _ n
    exact posted_quadratic_strict_growth x hn n
  · intro h
    have hbad := posted_quadratic_strict_growth x hn 1
    linarith

#print axioms quadratic_iteration_nonneg
#print axioms quadratic_iteration_strictMono_of_step
#print axioms quadratic_iteration_strictAnti_of_step
#print axioms quadratic_iteration_below_one_increasing
#print axioms quadratic_iteration_between_fixed_points_decreasing
#print axioms quadratic_iteration_above_two_increasing
#print axioms quadratic_iteration_fixed
#print axioms quadratic_iteration_invariant_interval
#print axioms quadratic_iteration_geometric_error
#print axioms quadratic_iteration_tendsto_one
#print axioms quadratic_iteration_linear_growth
#print axioms quadratic_iteration_tendsto_atTop
#print axioms quadratic_iteration_finite_limit_iff
#print axioms source_quadratic_monotonicity
#print axioms source_quadratic_dynamics
#print axioms posted_quadratic_strict_growth
#print axioms solution
