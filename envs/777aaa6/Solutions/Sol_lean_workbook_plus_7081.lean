-- Prove2me | solution 1 for lean_workbook_plus_7081
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:28:45.280445+00:00
-- url     : https://prove2.me/submissions/6688e69f-3db5-48e1-b8b8-b93374ce3a7b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem delayed_quadratic_step_bound (q M x y : ℝ) (hq : 0 ≤ q)
    (hyq : |y| ≤ q) (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |(y ^ 2 - x) / 2| ≤ ((q + 1) / 2) * M := by
  have hs : y ^ 2 ≤ q * M := by
    simpa only [← pow_two, sq_abs] using mul_le_mul hyq hy (abs_nonneg y) hq
  have ht := abs_sub (y ^ 2) x
  rw [abs_of_nonneg (sq_nonneg y)] at ht
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem delayed_quadratic_invariant (u : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : |u 0| ≤ q) (h1 : |u 1| ≤ q)
    (hr : ∀ n, u (n + 2) = ((u (n + 1)) ^ 2 - u n) / 2) (n : ℕ) : |u n| ≤ q := by
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih ih' =>
    rw [hr n]
    have hs := delayed_quadratic_step_bound q q (u n) (u (n + 1)) hq0 ih' ih ih'
    have hp := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith

theorem delayed_quadratic_pair_rate (u : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : |u 0| ≤ q) (h1 : |u 1| ≤ q)
    (hr : ∀ n, u (n + 2) = ((u (n + 1)) ^ 2 - u n) / 2) (k : ℕ) :
    |u (2 * k)| ≤ q * ((q + 1) / 2) ^ k ∧
    |u (2 * k + 1)| ≤ q * ((q + 1) / 2) ^ k := by
  let c : ℝ := (q + 1) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hi := delayed_quadratic_invariant u q hq0 hq1 h0 h1 hr
  change |u (2 * k)| ≤ q * c ^ k ∧ |u (2 * k + 1)| ≤ q * c ^ k
  induction k with
  | zero => simpa using And.intro h0 h1
  | succ k ih =>
    let M := q * c ^ k
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hA : |u (2 * k + 2)| ≤ c * M := by
      rw [hr (2 * k)]
      exact delayed_quadratic_step_bound q M _ _ hq0 (hi _) ih.1 ih.2
    have hAM : |u (2 * k + 2)| ≤ M := hA.trans (by nlinarith)
    have hB : |u (2 * k + 3)| ≤ c * M := by
      rw [show 2 * k + 3 = (2 * k + 1) + 2 by omega, hr]
      exact delayed_quadratic_step_bound q M _ _ hq0 (hi _) ih.2 hAM
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      show 2 * k + 2 + 1 = 2 * k + 3 by omega, pow_succ]
    dsimp [M] at hA hB
    constructor <;> nlinarith

theorem delayed_quadratic_rate (u : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : |u 0| ≤ q) (h1 : |u 1| ≤ q)
    (hr : ∀ n, u (n + 2) = ((u (n + 1)) ^ 2 - u n) / 2) (n : ℕ) :
    |u n| ≤ q * ((q + 1) / 2) ^ (n / 2) := by
  have hp := delayed_quadratic_pair_rate u q hq0 hq1 h0 h1 hr (n / 2)
  have hd := Nat.mod_add_div n 2
  have hm := Nat.mod_lt n (by norm_num : 0 < 2)
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
  · have hn : 2 * (n / 2) = n := by omega
    simpa only [hn] using hp.1
  · have hn : 2 * (n / 2) + 1 = n := by omega
    simpa only [hn] using hp.2

theorem delayed_quadratic_small_initial_converges (u : ℕ → ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (h0 : |u 0| ≤ q) (h1 : |u 1| ≤ q)
    (hr : ∀ n, u (n + 2) = ((u (n + 1)) ^ 2 - u n) / 2) :
    Tendsto u atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.2 fun k => eventually_atTop.2 ⟨2 * k, ?_⟩
    intro n hn
    omega
  have hp : Tendsto (fun n : ℕ => ((q + 1) / 2) ^ (n / 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (q + 1) / 2)
      (by linarith : (q + 1) / 2 < 1)).comp hd
  have ht : Tendsto (fun n : ℕ => q * ((q + 1) / 2) ^ (n / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul q
  have he := squeeze_zero (fun n => abs_nonneg (u n))
    (delayed_quadratic_rate u q hq0 hq1.le h0 h1 hr) ht
  apply (tendsto_iff_norm_sub_tendsto_zero (f := u) (b := (0 : ℝ))).mpr
  simpa only [sub_zero, Real.norm_eq_abs] using he

theorem delayed_quadratic_source_prefix (a : ℕ → ℝ) (h0 : a 0 = 2) (h1 : a 1 = -2)
    (hr : ∀ n, a (n + 2) = ((a (n + 1)) ^ 2 - a n) / 2) :
    a 2 = 1 ∧ a 3 = 3 / 2 ∧ a 4 = 5 / 8 ∧ a 5 = -(71 / 128) := by
  have h2 : a 2 = 1 := by rw [hr 0, h1, h0]; ring
  have h3 : a 3 = 3 / 2 := by rw [hr 1, h2, h1]; ring
  have h4 : a 4 = 5 / 8 := by rw [hr 2, h3, h2]; ring
  have h5 : a 5 = -(71 / 128) := by rw [hr 3, h4, h3]; ring
  exact ⟨h2, h3, h4, h5⟩

theorem delayed_quadratic_source_tail_rate (a : ℕ → ℝ) (h0 : a 0 = 2) (h1 : a 1 = -2)
    (hr : ∀ n, a (n + 2) = ((a (n + 1)) ^ 2 - a n) / 2) (n : ℕ) :
    |a (n + 4)| ≤ (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (n / 2) := by
  have hp := delayed_quadratic_source_prefix a h0 h1 hr
  have hs : ∀ k, a (k + 2 + 4) = ((a (k + 1 + 4)) ^ 2 - a (k + 4)) / 2 := by
    intro k
    convert hr (k + 4) using 1
  have h := delayed_quadratic_rate (fun k => a (k + 4)) (3 / 4) (by norm_num) (by norm_num)
    (by simpa only [zero_add, hp.2.2.1] using (show |(5 / 8 : ℝ)| ≤ 3 / 4 by norm_num))
    (by simpa only [hp.2.2.2] using (show |(-(71 / 128) : ℝ)| ≤ 3 / 4 by norm_num)) hs n
  norm_num at h ⊢
  exact h

theorem delayed_quadratic_source_converges (a : ℕ → ℝ) (h0 : a 0 = 2) (h1 : a 1 = -2)
    (hr : ∀ n, a (n + 2) = ((a (n + 1)) ^ 2 - a n) / 2) :
    Tendsto a atTop (𝓝 0) := by
  have hp := delayed_quadratic_source_prefix a h0 h1 hr
  have hs : ∀ k, a (k + 2 + 4) = ((a (k + 1 + 4)) ^ 2 - a (k + 4)) / 2 := by
    intro k
    convert hr (k + 4) using 1
  have ht := delayed_quadratic_small_initial_converges (fun k => a (k + 4)) (3 / 4)
    (by norm_num) (by norm_num)
    (by simpa only [zero_add, hp.2.2.1] using (show |(5 / 8 : ℝ)| ≤ 3 / 4 by norm_num))
    (by simpa only [hp.2.2.2] using (show |(-(71 / 128) : ℝ)| ≤ 3 / 4 by norm_num)) hs
  exact (tendsto_add_atTop_iff_nat 4).mp ht

noncomputable def delayedQuadraticOrbit (n : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℝ × ℝ) ((2 : ℝ), (-2 : ℝ))
    (fun _ p => (p.2, (p.2 ^ 2 - p.1) / 2)) n).1

theorem delayed_quadratic_orbit_zero : delayedQuadraticOrbit 0 = 2 := rfl

theorem delayed_quadratic_orbit_one : delayedQuadraticOrbit 1 = -2 := rfl

theorem delayed_quadratic_orbit_recurrence (n : ℕ) :
    delayedQuadraticOrbit (n + 2) =
      ((delayedQuadraticOrbit (n + 1)) ^ 2 - delayedQuadraticOrbit n) / 2 := rfl

theorem delayed_quadratic_orbit_converges : Tendsto delayedQuadraticOrbit atTop (𝓝 0) :=
  delayed_quadratic_source_converges _ rfl rfl delayed_quadratic_orbit_recurrence

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 2) (a2 : a 1 = -2)
    (a_rec : ∀ n, a (n + 1) = (a n) ^ 2 / 2 - a (n - 1) / 2) :
    ∃ l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - l| < ε := by
  have hr : ∀ n, a (n + 2) = ((a (n + 1)) ^ 2 - a n) / 2 := by
    intro n
    have h := a_rec (n + 1)
    simpa only [Nat.add_sub_cancel, sub_div] using h
  have ht := delayed_quadratic_source_converges a a1 a2 hr
  refine ⟨0, ?_⟩
  simpa only [Real.dist_eq] using Metric.tendsto_atTop.mp ht

#print axioms delayed_quadratic_step_bound
#print axioms delayed_quadratic_invariant
#print axioms delayed_quadratic_pair_rate
#print axioms delayed_quadratic_rate
#print axioms delayed_quadratic_small_initial_converges
#print axioms delayed_quadratic_source_prefix
#print axioms delayed_quadratic_source_tail_rate
#print axioms delayed_quadratic_source_converges
#print axioms delayedQuadraticOrbit
#print axioms delayed_quadratic_orbit_zero
#print axioms delayed_quadratic_orbit_one
#print axioms delayed_quadratic_orbit_recurrence
#print axioms delayed_quadratic_orbit_converges
#print axioms solution
