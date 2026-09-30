-- Prove2me | solution 1 for lean_workbook_plus_50566
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:39:49.02554+00:00
-- url     : https://prove2.me/submissions/50b9945f-e548-4dfa-8b85-2a10c7024602

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (n a b : ℕ) (ha : a ^ 2 + b ^ 2 = 2 ^ n)
    (hb : 2 ≤ n) : Even a ∧ Even b := by
  have hd : 4 ∣ 2 ^ n := by simpa using pow_dvd_pow (2 : ℕ) hb
  have hm := congrArg (fun x : ℕ => x % 4) ha
  change (a ^ 2 + b ^ 2) % 4 = 2 ^ n % 4 at hm
  rw [Nat.mod_eq_zero_of_dvd hd, Nat.add_mod, Nat.pow_mod a, Nat.pow_mod b] at hm
  have ha4 := Nat.mod_lt a (by decide : 0 < 4)
  have hb4 := Nat.mod_lt b (by decide : 0 < 4)
  interval_cases h1 : a % 4 <;> interval_cases h2 : b % 4 <;>
    norm_num [h1, h2] at hm <;> simp only [Nat.even_iff] <;> omega

theorem axes_or_diagonal (n a b : ℕ) (h : a ^ 2 + b ^ 2 = 2 ^ n) :
    a = 0 ∨ b = 0 ∨ a = b := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · interval_cases n
      · norm_num at h
        by_cases ha : a = 0
        · exact Or.inl ha
        · right
          left
          have ha1 : 1 ≤ a := by omega
          nlinarith
      · norm_num at h
        have ha : a ≤ 1 := by nlinarith
        have hb : b ≤ 1 := by nlinarith
        omega
    · have he := solution n a b h (by omega)
      rcases he.1 with ⟨u, rfl⟩
      rcases he.2 with ⟨v, rfl⟩
      have hp : 2 ^ n = 4 * 2 ^ (n - 2) := by
        calc
          2 ^ n = 2 ^ (2 + (n - 2)) := by congr 1; omega
          _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; rfl
      rw [hp] at h
      have huv : u ^ 2 + v ^ 2 = 2 ^ (n - 2) := by nlinarith
      rcases ih (n - 2) (by omega) u v huv with hu | hv | huv
      · left; omega
      · right; left; omega
      · right; right; omega

#print axioms solution
#print axioms axes_or_diagonal
