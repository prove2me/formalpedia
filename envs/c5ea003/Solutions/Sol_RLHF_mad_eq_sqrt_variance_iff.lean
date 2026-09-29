-- Prove2me | solution 1 for RLHF.mad_eq_sqrt_variance_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:28:49.917897+00:00
-- url     : https://prove2.me/submissions/f0466eb0-6a0c-4091-a828-2eb72420a7a3

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
    mad p f = Real.sqrt (variance p f) ↔ ∀ y, |f y - mean p f| = mad p f := by
  obtain ⟨hpos, hsum⟩ := hp
  set μ := mean p f with hμ
  set m := mad p f with hm
  have hmad : m = ∑ y, p y * |f y - μ| := rfl
  -- `(f - μ)² = |f - μ|²`, so the variance is the second moment of the absolute deviation
  have hvar : variance p f = ∑ y, p y * |f y - μ| ^ 2 := by
    show ∑ y, p y * (f y - mean p f) ^ 2 = ∑ y, p y * |f y - μ| ^ 2
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sq_abs]
  have hm0 : 0 ≤ m := by
    rw [hmad]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hpos y).le (abs_nonneg _)
  -- the gap between variance and `m²` is a sum of squared deviations from `m`
  have hgap : variance p f - m ^ 2 = ∑ y, p y * (|f y - μ| - m) ^ 2 := by
    rw [hvar]
    have e : ∀ y, p y * (|f y - μ| - m) ^ 2
        = p y * |f y - μ| ^ 2 - 2 * m * (p y * |f y - μ|) + m ^ 2 * p y := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hmad, hsum]
    ring
  constructor
  · -- equality forces every squared deviation from `m` to vanish
    intro heq
    have hsq : m ^ 2 = variance p f := by
      rw [heq, Real.sq_sqrt]
      rw [hvar]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hpos y).le (sq_nonneg _)
    have hzero : ∑ y, p y * (|f y - μ| - m) ^ 2 = 0 := by rw [← hgap, hsq]; ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hpos y).le (sq_nonneg (|f y - μ| - m)))).mp hzero
    intro y
    have hy := hterm y (Finset.mem_univ y)
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h (ne_of_gt (hpos y))
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
  · -- constant absolute deviation makes the gap zero
    intro hconst
    have hzero : ∑ y, p y * (|f y - μ| - m) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hconst y]
      ring
    have hvm : variance p f = m ^ 2 := by linarith [hgap, hzero]
    rw [hvm, Real.sqrt_sq hm0]
