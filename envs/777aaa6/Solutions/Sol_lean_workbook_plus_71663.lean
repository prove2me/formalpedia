-- Prove2me | solution 1 for lean_workbook_plus_71663
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:49.654772+00:00
-- url     : https://prove2.me/submissions/3a1c3fd4-2d7f-4b0f-bcf7-edac6343415b

import Mathlib

theorem solution (x : ℕ) (h₀ : 2^x ≡ 1 [MOD 4]) : x = 0 := by
  cases x with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => norm_num [Nat.ModEq] at h₀
    | succ n =>
      exfalso
      have hd : 4 ∣ 2 ^ (n + 1 + 1) := by
        refine ⟨2 ^ n, ?_⟩
        simp only [pow_succ]
        ring
      have hz := Nat.mod_eq_zero_of_dvd hd
      change 2 ^ (n + 1 + 1) % 4 = 1 % 4 at h₀
      norm_num [hz] at h₀

#print axioms solution
