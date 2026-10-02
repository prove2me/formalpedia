-- Prove2me | solution 1 for BookSixth.latin_asymptotic_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T17:37:08.398167+00:00
-- url     : https://prove2.me/submissions/3bddbec9-6233-4191-ad47-23483d2ceea5

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators Topology
open Filter Finset BookSixth

namespace BookLatinAnalysis

noncomputable def a (n : ℕ) : ℝ := Real.log (n.factorial : ℝ) / n - Real.log n

theorem tendsto_a : Tendsto a atTop (𝓝 (-1)) := by
  obtain ⟨c, hc, hlim⟩ := Stirling.stirlingSeq_has_pos_limit_a
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := (hlim.log (ne_of_gt hc)).div_atTop hn
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  have hconst : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h := (hsmall.add ((hconst.add hlog).div_const 2)).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have heq : (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / n +
      (Real.log 2 / n + Real.log n / n) / 2 - 1) =ᶠ[atTop] a := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) (ne_of_gt hnR),
      Real.log_div (ne_of_gt hnR) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
    dsimp [a]
    field_simp
    <;> ring
  simpa using h.congr' heq

theorem sum_Icc_shift (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, f k) = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

theorem sum_log_nat (n : ℕ) :
    (∑ k ∈ Icc 1 n, Real.log (k : ℝ)) = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

theorem tendsto_average :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / (n : ℝ)) atTop (𝓝 (-1)) := by
  have h := (tendsto_a.comp (tendsto_add_atTop_nat 1)).cesaro
  simpa [Function.comp_def, sum_Icc_shift, div_eq_mul_inv, mul_comm] using h

noncomputable def upper (n : ℕ) : ℝ :=
  ∏ k ∈ Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))

theorem upper_pos (n : ℕ) : 0 < upper n := by
  apply Finset.prod_pos
  intro k hk
  exact Real.rpow_pos_of_pos (by positivity) _

theorem log_upper (n : ℕ) (hn : 0 < n) :
    Real.log (upper n) / (n : ℝ)^2 - Real.log n =
      a n + (∑ k ∈ Icc 1 n, a k) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : (∑ k ∈ Icc 1 n, Real.log (k.factorial : ℝ) / k) =
      (∑ k ∈ Icc 1 n, a k) + Real.log (n.factorial : ℝ) := by
    rw [← sum_log_nat, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    dsimp [a]
    ring
  have hlog : Real.log (upper n) =
      (n : ℝ) * ∑ k ∈ Icc 1 n, Real.log (k.factorial : ℝ) / k := by
    rw [upper, Real.log_prod (fun k _ => ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)),
      mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [Real.log_rpow (by positivity)]
    ring
  rw [hlog, hsum]
  dsimp [a]
  field_simp
  <;> ring

end BookLatinAnalysis

theorem solution (hlow : ∀ n : ℕ, 0 < n → (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n * n) ≤ (latinCount n : ℝ)) (hup : ∀ n : ℕ, 0 < n → (latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) :
    Filter.Tendsto (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ))
      Filter.atTop (nhds (Real.exp (-2))) := by
  let b (n : ℕ) : ℝ := Real.log (latinCount n : ℝ) / (n : ℝ)^2 - Real.log n
  have hpos (n : ℕ) (hn : 0 < n) : 0 < (latinCount n : ℝ) := by
    exact lt_of_lt_of_le (by positivity) (hlow n hn)
  have hlo : ∀ᶠ n : ℕ in atTop, 2 * BookLatinAnalysis.a n ≤ b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnN : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
    have h := Real.log_le_log (by positivity) (hlow n hnN)
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    push_cast at h
    have h' := (div_le_div_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (n : ℝ)^2))
    have heq : ((2 * (n : ℝ)) * Real.log (n.factorial : ℝ) -
        ((n : ℝ) * n) * Real.log n) / (n : ℝ)^2 - Real.log n =
        2 * BookLatinAnalysis.a n := by
      dsimp [BookLatinAnalysis.a]
      field_simp
      <;> ring
    dsimp [b]
    linarith
  have hhi : ∀ᶠ n : ℕ in atTop, b n ≤
      BookLatinAnalysis.a n + (∑ k ∈ Icc 1 n, BookLatinAnalysis.a k) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnN : 0 < n := by omega
    have h := Real.log_le_log (hpos n hnN) (hup n hnN)
    have h' := div_le_div_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (n : ℝ)^2)
    have hu := BookLatinAnalysis.log_upper n hnN
    dsimp [BookLatinAnalysis.upper] at hu
    dsimp [b]
    linarith
  have hb : Tendsto b atTop (𝓝 (-2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using BookLatinAnalysis.tendsto_a.const_mul 2)
      (by convert BookLatinAnalysis.tendsto_a.add BookLatinAnalysis.tendsto_average using 1 <;> norm_num)
      hlo hhi
  have heq : (fun n => Real.exp (b n)) =ᶠ[atTop]
      (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnN : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
    dsimp [b]
    rw [Real.exp_sub, Real.exp_log hnR, Real.rpow_def_of_pos (hpos n hnN)]
    congr 2
    ring
  exact hb.rexp.congr' heq
