-- Prove2me | solution 1 for lean_workbook_plus_18354
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:48:43.734132+00:00
-- url     : https://prove2.me/submissions/e7b81d1a-ee44-46b7-900c-320926c65e74

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology

theorem nonnegative_power_increment_mono {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (n : ℕ) : (a + c) ^ n - a ^ n ≤ (b + c) ^ n - b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 0 ≤ b := ha.trans hab
    have hd : 0 ≤ (a + c) ^ n - a ^ n :=
      sub_nonneg.mpr (pow_le_pow_left₀ ha (le_add_of_nonneg_right hc) n)
    calc
      (a + c) ^ (n + 1) - a ^ (n + 1) =
          (a + c) * ((a + c) ^ n - a ^ n) + c * a ^ n := by ring
      _ ≤ (b + c) * ((b + c) ^ n - b ^ n) + c * b ^ n :=
        add_le_add (mul_le_mul (add_le_add hab le_rfl) ih hd (add_nonneg hb hc))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab n) hc)
      _ = (b + c) ^ (n + 1) - b ^ (n + 1) := by ring

noncomputable def rootMaxSequence (n : ℕ) (x : ℝ) : ℝ :=
  (2 ^ n + |x| ^ n) ^ (1 / (n : ℝ))

theorem rootMaxSequence_nonneg (n : ℕ) (x : ℝ) : 0 ≤ rootMaxSequence n x := by
  exact Real.rpow_nonneg (by positivity) _

theorem rootMaxSequence_pow {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    (rootMaxSequence n x) ^ n = 2 ^ n + |x| ^ n := by
  unfold rootMaxSequence
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (by positivity) hn

theorem rootMaxSequence_lower {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    max 2 |x| ≤ rootMaxSequence n x := by
  have htwo := Real.rpow_le_rpow (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n)
    (le_add_of_nonneg_right (pow_nonneg (abs_nonneg x) n))
    (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  have hx := Real.rpow_le_rpow (pow_nonneg (abs_nonneg x) n)
    (le_add_of_nonneg_left (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n))
    (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  rw [Real.pow_rpow_inv_natCast (by norm_num) hn] at htwo
  rw [Real.pow_rpow_inv_natCast (abs_nonneg x) hn] at hx
  simpa only [rootMaxSequence, one_div] using max_le htwo hx

theorem rootMaxSequence_at_two {n : ℕ} (hn : n ≠ 0) :
    rootMaxSequence n 2 = 2 * (2 : ℝ) ^ (1 / (n : ℝ)) := by
  unfold rootMaxSequence
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [show (2 : ℝ) ^ n + 2 ^ n = 2 ^ n * 2 by ring,
    Real.mul_rpow (by positivity) (by norm_num), one_div,
    Real.pow_rpow_inv_natCast (by norm_num) hn]

theorem rootMaxSequence_error_bound {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |rootMaxSequence n x - max 2 (|x|)| ≤
      2 * ((2 : ℝ) ^ (1 / (n : ℝ)) - 1) := by
  let D := rootMaxSequence n 2 - 2
  have hD : 0 ≤ D := by
    have h := rootMaxSequence_lower hn 2
    simp only [abs_of_pos (show (0 : ℝ) < 2 by norm_num), max_self] at h
    exact sub_nonneg.mpr h
  have hbound : rootMaxSequence n x - max 2 |x| ≤ D := by
    rcases le_total |x| 2 with hx | hx
    · have hr : rootMaxSequence n x ≤ rootMaxSequence n 2 := by
        apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        simp only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        exact add_le_add le_rfl (pow_le_pow_left₀ (abs_nonneg x) hx n)
      rw [max_eq_left hx]
      exact sub_le_sub_right hr 2
    · have hinc := nonnegative_power_increment_mono (by norm_num : (0 : ℝ) ≤ 2) hx hD n
      have hsum : 2 + D = rootMaxSequence n 2 := by dsimp [D]; ring
      rw [hsum, rootMaxSequence_pow hn] at hinc
      simp only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hinc
      have hpow : (2 : ℝ) ^ n + |x| ^ n ≤ (|x| + D) ^ n := by linarith
      have hr := Real.rpow_le_rpow (show 0 ≤ (2 : ℝ) ^ n + |x| ^ n by positivity)
        hpow (show 0 ≤ (n : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (add_nonneg (abs_nonneg x) hD) hn] at hr
      have hr' : rootMaxSequence n x ≤ |x| + D := by
        simpa only [rootMaxSequence, one_div] using hr
      rw [max_eq_right hx]
      linarith
  rw [abs_of_nonneg (sub_nonneg.mpr (rootMaxSequence_lower hn x))]
  convert hbound using 1
  dsimp [D]
  rw [rootMaxSequence_at_two hn]
  ring

theorem rootMaxSequence_error_attained {n : ℕ} (hn : n ≠ 0) :
    |rootMaxSequence n 2 - max 2 (|(2 : ℝ)|)| =
      2 * ((2 : ℝ) ^ (1 / (n : ℝ)) - 1) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (rootMaxSequence_lower hn 2)),
    rootMaxSequence_at_two hn]
  simp only [abs_of_pos (show (0 : ℝ) < 2 by norm_num), max_self]
  ring

theorem rootMaxSequence_uniform_bound_iff {n : ℕ} (hn : n ≠ 0) (M : ℝ) :
    (∀ x : ℝ, |rootMaxSequence n x - max 2 (|x|)| ≤ M) ↔
      2 * ((2 : ℝ) ^ (1 / (n : ℝ)) - 1) ≤ M := by
  constructor
  · intro h
    simpa only [rootMaxSequence_error_attained hn] using h 2
  · intro h x
    exact (rootMaxSequence_error_bound hn x).trans h

theorem rootMaxSequence_error_tendsto_zero :
    Tendsto (fun n : ℕ => 2 * ((2 : ℝ) ^ (1 / (n : ℝ)) - 1)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl (by norm_num))
  simpa only [Real.rpow_zero, sub_self, mul_zero] using (h.sub_const 1).const_mul 2

theorem rootMaxSequence_uniform_convergence :
    TendstoUniformly rootMaxSequence (fun x : ℝ => max 2 |x|) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [rootMaxSequence_error_tendsto_zero.eventually_lt_const hε,
    eventually_ge_atTop 1] with n hn hnpos x
  have hn0 : n ≠ 0 := by omega
  rw [Real.dist_eq, abs_sub_comm]
  exact (rootMaxSequence_error_bound hn0 x).trans_lt hn

theorem solution (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) (f_n : ℝ)
    (hf_n : f_n = (2 ^ n + |x| ^ n) ^ (1 / n)) :
    ∃ l : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |f_n - l| < ε := by
  refine ⟨f_n, fun ε hε => ⟨0, fun n hn => ?_⟩⟩
  simpa only [sub_self, abs_zero] using hε

#print axioms nonnegative_power_increment_mono
#print axioms rootMaxSequence
#print axioms rootMaxSequence_nonneg
#print axioms rootMaxSequence_pow
#print axioms rootMaxSequence_lower
#print axioms rootMaxSequence_at_two
#print axioms rootMaxSequence_error_bound
#print axioms rootMaxSequence_error_attained
#print axioms rootMaxSequence_uniform_bound_iff
#print axioms rootMaxSequence_error_tendsto_zero
#print axioms rootMaxSequence_uniform_convergence
#print axioms solution
