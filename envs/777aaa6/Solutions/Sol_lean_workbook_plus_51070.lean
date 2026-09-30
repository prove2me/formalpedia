-- Prove2me | solution 1 for lean_workbook_plus_51070
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:00.387808+00:00
-- url     : https://prove2.me/submissions/78b72148-26e5-4e76-a389-d9ae55b3de37

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : 5 ≤ p) (hp' : Nat.Prime p) :
    ∃ m n : ℕ, (m + n ≤ (p + 1) / 2) ∧ (p : ℤ) ∣ (2 ^ n * 3 ^ m - 1) :=
  ⟨0, 0, by omega, by norm_num⟩
