-- Prove2me | solution 1 for lean_workbook_plus_27292
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:40.214183+00:00
-- url     : https://prove2.me/submissions/597aad19-c3d5-44cd-9e54-23f0c94201d3

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : ((n + 1) / n)^n ≤ 3 := by
  rcases n with _ | _ | n
  · simp
  · simp
  · have h0 : (n + 1 + 1 + 1) / (n + 1 + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h0, one_pow]
    norm_num
