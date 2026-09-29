-- Prove2me | solution 1 for waiting_time_density_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:12:17.172355+00:00
-- url     : https://prove2.me/submissions/c5527157-b758-4dd8-90e8-64cfdf8f991c

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
open MeasureTheory Set

theorem solution (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam) (Set.Ioi (0:ℝ)) := by
  set D : ℝ := |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam| with hD
  have hgint : IntegrableOn (fun t : ℝ => D * Real.exp (-lam * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul D
  have hcont : Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam) := by fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ mp ≤ 1 := pow_le_one₀ hq0 hq1
  have hpm0 : (0:ℝ) ≤ (1 - Real.exp (-(lam * t))) ^ mp := pow_nonneg hq0 _
  have hNmp : 1 ≤ N - mp := by omega
  have hpe : (Real.exp (-(lam * t))) ^ (N - mp) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNmp
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - mp) := pow_nonneg he.le _
  rw [Real.norm_eq_abs]
  have habs : |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam|
      = D * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) := by
    rw [hD]
    rw [show (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam
        = ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
            * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) (by positivity)]
  rw [habs]
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; exact abs_nonneg _
  rw [show D * Real.exp (-lam * t) = D * Real.exp (-(lam * t)) by ring]
  apply mul_le_mul_of_nonneg_left _ hDnn
  calc (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)
      ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * t)) := by ring
