-- Prove2me | solution 1 for lean_workbook_plus_21470
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:31:54.919627+00:00
-- url     : https://prove2.me/submissions/b29f4cee-476b-41ad-a480-6c4721ef4904

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Topology

theorem asymptotic_line_intercept_iff (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto (fun x => f x - (a * x + b)) atTop (𝓝 0) ↔
      Tendsto (fun x => f x - a * x) atTop (𝓝 b) := by
  constructor
  · intro h
    simpa only [sub_add_eq_sub_sub, sub_add_cancel, zero_add] using h.add_const b
  · intro h
    simpa only [sub_add_eq_sub_sub, sub_self] using h.sub_const b

theorem asymptotic_line_slope (f : ℝ → ℝ) (a b : ℝ)
    (h : Tendsto (fun x => f x - (a * x + b)) atTop (𝓝 0)) :
    Tendsto (fun x => f x / x) atTop (𝓝 a) := by
  have hi := (asymptotic_line_intercept_iff f a b).mp h
  have hz : Tendsto (fun x => (f x - a * x) / x) atTop (𝓝 0) := hi.div_atTop tendsto_id
  have ht : Tendsto (fun x => (f x - a * x) / x + a) atTop (𝓝 a) := by
    simpa only [zero_add] using hz.add_const a
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [hx.ne']
  ring

theorem asymptotic_line_characterization (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto (fun x => f x - (a * x + b)) atTop (𝓝 0) ↔
      Tendsto (fun x => f x / x) atTop (𝓝 a) ∧
      Tendsto (fun x => f x - a * x) atTop (𝓝 b) := by
  exact ⟨fun h => ⟨asymptotic_line_slope f a b h, (asymptotic_line_intercept_iff f a b).mp h⟩,
    fun h => (asymptotic_line_intercept_iff f a b).mpr h.2⟩

theorem asymptotic_line_unique (f : ℝ → ℝ) (a b c d : ℝ)
    (h : Tendsto (fun x => f x - (a * x + b)) atTop (𝓝 0))
    (h' : Tendsto (fun x => f x - (c * x + d)) atTop (𝓝 0)) : a = c ∧ b = d := by
  have hac := tendsto_nhds_unique (asymptotic_line_slope f a b h) (asymptotic_line_slope f c d h')
  subst c
  exact ⟨rfl, tendsto_nhds_unique ((asymptotic_line_intercept_iff f a b).mp h)
    ((asymptotic_line_intercept_iff f a d).mp h')⟩

theorem asymptotic_line_ratio_error (f : ℝ → ℝ) (a b M x : ℝ) (hx : 0 < x)
    (h : |f x - (a * x + b)| ≤ M) : |f x / x - a| ≤ (|b| + M) / x := by
  have he : f x / x - a = (b + (f x - (a * x + b))) / x := by
    field_simp [hx.ne']
    ring
  rw [he, abs_div, abs_of_pos hx]
  exact div_le_div_of_nonneg_right
    ((abs_add_le b (f x - (a * x + b))).trans (add_le_add (le_refl |b|) h)) hx.le

theorem asymptotic_line_eventual_rate (f : ℝ → ℝ) (a b : ℝ)
    (h : Tendsto (fun x => f x - (a * x + b)) atTop (𝓝 0)) :
    ∀ᶠ x in atTop, 0 < x ∧ |f x / x - a| ≤ (|b| + 1) / x := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h 1 (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop M] with x hx hxM
  refine ⟨hx, asymptotic_line_ratio_error f a b 1 x hx ?_⟩
  have hm := hM x hxM
  simpa only [Real.dist_eq, sub_zero] using hm.le

theorem real_atTop_limit_nat_threshold_iff (f : ℝ → ℝ) (L : ℝ) :
    Tendsto f atTop (𝓝 L) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ x > (N : ℝ), |f x - L| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt M
    refine ⟨N, fun x hx => ?_⟩
    simpa only [Real.dist_eq] using hM x (show M ≤ x by linarith)
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨(N : ℝ) + 1, fun x hx => ?_⟩
    simpa only [Real.dist_eq] using hN x (show (N : ℝ) < x by linarith)

theorem asymptotic_line_epsilon_slope (f : ℝ → ℝ) (a b : ℝ)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ x > (N : ℝ), |f x - (a * x + b)| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ x > (N : ℝ), |f x / x - a| < ε := by
  apply (real_atTop_limit_nat_threshold_iff (fun x => f x / x) a).mp
  apply asymptotic_line_slope f a b
  apply (real_atTop_limit_nat_threshold_iff (fun x => f x - (a * x + b)) 0).mpr
  simpa only [sub_zero] using h

theorem asymptotic_line_nat_slope (u : ℕ → ℝ) (a b : ℝ)
    (h : Tendsto (fun n => u n - (a * n + b)) atTop (𝓝 0)) :
    Tendsto (fun n => u n / n) atTop (𝓝 a) := by
  have hi : Tendsto (fun n => u n - a * n) atTop (𝓝 b) := by
    simpa only [sub_add_eq_sub_sub, sub_add_cancel, zero_add] using h.add_const b
  have hz : Tendsto (fun n => (u n - a * n) / n) atTop (𝓝 0) :=
    hi.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n => (u n - a * n) / n + a) atTop (𝓝 a) := by
    simpa only [zero_add] using hz.add_const a
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]
  ring

theorem asymptotic_line_nat_epsilon_slope (u : ℕ → ℝ) (a b : ℝ)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - (a * n + b)| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n / n - a| < ε := by
  have ht : Tendsto (fun n => u n - (a * n + b)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N + 1, fun n hn => ?_⟩
    simpa only [Real.dist_eq, sub_zero] using hN n (show N < n by omega)
  have hs := asymptotic_line_nat_slope u a b ht
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hs ε hε
  exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn.le⟩

theorem solution (a b : ℝ) (f : ℝ → ℝ) (_h1 : ∀ x, f x ≠ 0) (_h2 : ∀ x, x ≠ 0) :
    (∀ ε > 0, ∃ N : ℕ, ∀ x > N, |f x - (a * x + b)| < ε) →
      ∀ ε > 0, ∃ N : ℕ, ∀ x > N, |f x / x - a| < ε :=
  asymptotic_line_nat_epsilon_slope (fun n => f n) a b

#print axioms asymptotic_line_intercept_iff
#print axioms asymptotic_line_slope
#print axioms asymptotic_line_characterization
#print axioms asymptotic_line_unique
#print axioms asymptotic_line_ratio_error
#print axioms asymptotic_line_eventual_rate
#print axioms real_atTop_limit_nat_threshold_iff
#print axioms asymptotic_line_epsilon_slope
#print axioms asymptotic_line_nat_slope
#print axioms asymptotic_line_nat_epsilon_slope
#print axioms solution
