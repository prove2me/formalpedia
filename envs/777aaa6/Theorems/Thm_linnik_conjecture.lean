-- Prove2me | Theorems.Thm_linnik_conjecture
-- name    : linnik_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:00:14.498988+00:00
-- url     : https://prove2.me/theorems/0aaea4dc-199e-4475-b539-da2700a24db9
-- statement:
--   Linnik's conjecture: For any arithmetic progression {a, a+q, a+2q,...} with gcd(a,q)=1, the smallest prime in this progression is at most q². Currently only q^L with L ≤ 5 is proved (Xylouris 2011). The conjectured value L=2 is open.
-- source:
--   https://en.wikipedia.org/wiki/Linnik%27s_theorem

import Mathlib

import Mathlib

-- Linnik's theorem (proved) and conjecture on the first prime in arithmetic progressions
-- The Linnik constant L: for gcd(a, q) = 1, the smallest prime p ≡ a (mod q) satisfies p ≤ q^L
-- Conjecture: L = 2 (the smallest prime is at most q²)
-- Known: L ≤ 5 (Xylouris 2011)
theorem linnik_conjecture :
    ∀ q a : ℕ, 1 < q → Nat.Coprime a q →
      ∃ p : ℕ, Nat.Prime p ∧ p % q = a % q ∧ p ≤ q ^ 2 := by
  sorry
