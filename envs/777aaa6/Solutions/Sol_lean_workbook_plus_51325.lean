-- Prove2me | solution 1 for lean_workbook_plus_51325
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:42:12.17129+00:00
-- url     : https://prove2.me/submissions/bc3b38ff-ad06-4f01-aa5f-9ba87c171cbf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, ∀ x, f n x = if 0 ≤ x ∧ x ≤ 1 / n then Real.sqrt n else 0) :
    ¬ ∀ ε > 0, ∃ N, ∀ n > N, ∀ x ∈ Set.Icc 0 1, |f n x - 0| < ε := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  have hh := hN (N + 1) (by omega) 0 (by norm_num)
  rw [hf (N + 1) 0, if_pos ⟨le_rfl, by positivity⟩, sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  have hc : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  exact (not_lt_of_ge (Real.one_le_sqrt.mpr hc)) hh

#print axioms solution
