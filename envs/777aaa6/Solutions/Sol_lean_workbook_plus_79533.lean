-- Prove2me | solution 1 for lean_workbook_plus_79533
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:15.435104+00:00
-- url     : https://prove2.me/submissions/7d502cf7-65a2-4be6-bbf7-01f1edb5f0e9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (u : ℕ → ℝ) (a b : ℕ → ℝ)
    (ha : a = fun n : ℕ => u (2 * n - 1))
    (hb : b = fun n : ℕ => u (2 * n)) :
    u = fun n => if n % 2 = 0 then b (n / 2) else a ((n + 1) / 2) := by
  subst a
  subst b
  funext n
  split_ifs with hn
  · congr 1
    omega
  · congr 1
    omega

#print axioms solution
