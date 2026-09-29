-- Prove2me | solution 1 for lean_workbook_plus_7344
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:01.811008+00:00
-- url     : https://prove2.me/submissions/444bccf5-6e30-4a03-816c-db000139f1ee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {m : ℤ} (f : ℤ → ℤ) (hf: f = fun n => if n % 2 = 0 then n-1 else n+1) : ∀ n ≤ 2*m, f n = if n % 2 = 0 then n-1 else n+1 := by
  (intros; simp_all)
