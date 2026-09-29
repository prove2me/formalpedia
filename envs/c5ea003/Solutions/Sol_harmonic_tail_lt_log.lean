-- Prove2me | solution 1 for harmonic_tail_lt_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:47:35.715692+00:00
-- url     : https://prove2.me/submissions/ac56db99-97bb-4c02-bc85-b96b4c067c43

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace HarmLog

-- per-term strict bound: 1/(j+1) < log((j+1)/j)  for j ≥ 1
theorem term_lt (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j + 1) < Real.log ((j+1) / j) := by
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  -- use log(j/(j+1)) < j/(j+1) - 1
  have hx : (0:ℝ) < (j:ℝ) / (j+1) := by positivity
  have hxne : (j:ℝ) / (j+1) ≠ 1 := by
    have hd : (j:ℝ) / (j+1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hkey := Real.log_lt_sub_one_of_pos hx hxne
  -- log(j/(j+1)) = -log((j+1)/j)
  have hlog : Real.log ((j:ℝ) / (j+1)) = - Real.log (((j:ℝ)+1) / j) := by
    rw [← Real.log_inv]; congr 1
    rw [inv_div]
  rw [hlog] at hkey
  have hrhs : (j:ℝ) / (j+1) - 1 = - (1 / ((j:ℝ)+1)) := by
    field_simp; ring
  rw [hrhs] at hkey
  linarith

-- telescoping log:  ∑_{j=a}^{b-1} log((j+1)/j) = log(b/a)   ... here stated as the harmonic-vs-log bound
-- ∑_{j ∈ Ico a b} 1/(j+1) < log(b/a) for 1 ≤ a < b
theorem harmonic_tail_lt_log (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) := by
  -- ∑ log((j+1)/j) telescopes to log(b/a)
  have htel : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+1) / j)) = Real.log ((b:ℝ)/a) := by
    have hcongr : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+1) / j))
        = ∑ j ∈ Finset.Ico a b, (Real.log ((j:ℝ)+1) - Real.log (j:ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : 1 ≤ j := by omega
      have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hcongr]
    -- telescoping sum of f(j+1)-f(j) with f = log
    have := Finset.sum_Ico_eq_sub (fun j => Real.log (j:ℝ)) (le_of_lt hab)
    -- ∑_{Ico a b} (g(j+1)-g(j)) = g(b) - g(a)
    rw [Finset.sum_Ico_eq_sum_range]
    have hstep : (∑ i ∈ Finset.range (b - a), (Real.log (((a+i:ℕ):ℝ)+1) - Real.log ((a+i:ℕ):ℝ)))
        = ∑ i ∈ Finset.range (b - a),
            ((fun k => Real.log ((a+k:ℕ):ℝ)) (i+1) - (fun k => Real.log ((a+k:ℕ):ℝ)) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only []
      have : ((a + (i+1) : ℕ) : ℝ) = ((a+i:ℕ):ℝ) + 1 := by push_cast; ring
      rw [this]
    rw [hstep, Finset.sum_range_sub (fun k => Real.log ((a+k:ℕ):ℝ)) (b-a)]
    have hba : a + (b - a) = b := by omega
    have hb1 : (1:ℕ) ≤ b := by omega
    rw [show (a + (b-a) : ℕ) = b from hba, Nat.add_zero]
    have hbR : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have haR : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    rw [Real.log_div hbR.ne' haR.ne']
  rw [← htel]
  apply Finset.sum_lt_sum_of_nonempty
  · rw [Finset.nonempty_Ico]; exact hab
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact term_lt j (by omega)

end HarmLog

theorem solution (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) :=
  HarmLog.harmonic_tail_lt_log a b ha hab
