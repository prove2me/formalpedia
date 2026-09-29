-- Prove2me | solution 1 for lean_workbook_plus_9417
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:05.931469+00:00
-- url     : https://prove2.me/submissions/47823a08-b696-476b-b5d3-ff2bcc34f748

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℕ → ℝ → ℝ) (f_lim : ℝ → ℝ) (hf : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n x - f_lim x| < ε) : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n x - f_lim x| < ε := by
  (intros; simp_all)
