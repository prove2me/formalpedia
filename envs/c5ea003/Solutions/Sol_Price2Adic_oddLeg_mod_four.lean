-- Prove2me | solution 1 for Price2Adic.oddLeg_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:52:36.279125+00:00
-- url     : https://prove2.me/submissions/9aa77f76-11d0-42fe-a440-32bc6725b491

import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

open Price2Adic

private lemma sq_mod_four_of_even {k : ℕ} (h : k % 2 = 0) : (k ^ 2) % 4 = 0 := by
  have : k % 4 = 0 ∨ k % 4 = 2 := by omega
  rcases this with h4 | h4 <;> simp [pow_two, Nat.mul_mod, h4]

private lemma sq_mod_four_of_odd {k : ℕ} (h : k % 2 = 1) : (k ^ 2) % 4 = 1 := by
  have : k % 4 = 1 ∨ k % 4 = 3 := by omega
  rcases this with h4 | h4 <;> simp [pow_two, Nat.mul_mod, h4]

private lemma sub_mod_four (a b : ℕ) (hle : b ≤ a) (ha : a % 4 = 0) (hb : b % 4 = 1) :
    (a - b) % 4 = 3 := by omega

private lemma sub_mod_four' (a b : ℕ) (hle : b ≤ a) (ha : a % 4 = 1) (hb : b % 4 = 0) :
    (a - b) % 4 = 1 := by omega

theorem solution (p : ℕ × ℕ) (hp : Valid p) :
    (letterOf p = .A ∧ oddLeg p % 4 = 1) ∨ (letterOf p ≠ .A ∧ oddLeg p % 4 = 3) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, _hg, hpar⟩ := hp
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hlt) 2
  unfold letterOf oddLeg
  by_cases hn2 : n % 2 = 0
  · left
    refine ⟨by simp [hn2], ?_⟩
    have hm1 : m % 2 = 1 := by omega
    exact sub_mod_four' (m ^ 2) (n ^ 2) hle (sq_mod_four_of_odd hm1) (sq_mod_four_of_even hn2)
  · right
    constructor
    · intro hA
      simp [hn2] at hA
      split_ifs at hA <;> cases hA
    · have hm0 : m % 2 = 0 := by omega
      have hn1 : n % 2 = 1 := by omega
      exact sub_mod_four (m ^ 2) (n ^ 2) hle (sq_mod_four_of_even hm0) (sq_mod_four_of_odd hn1)
