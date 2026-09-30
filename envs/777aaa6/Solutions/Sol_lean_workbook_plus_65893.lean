-- Prove2me | solution 1 for lean_workbook_plus_65893
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:31.851617+00:00
-- url     : https://prove2.me/submissions/37fc8c75-f3c1-4bb2-98ba-fb14c237f1a9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution : ∀ n : ℤ, n % 3 = 0 →
    (3 * n * (n + 1) + 7) % 9 = 7 % 9 := by
  intro n h
  have hn : n = 3 * (n / 3) := by omega
  have he : 3 * n * (n + 1) + 7 = 9 * ((n / 3) * (3 * (n / 3) + 1)) + 7 := by
    conv_lhs => rw [hn]
    ring
  rw [he]
  omega
