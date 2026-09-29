-- Prove2me | Theorems.Thm_jesmanowicz_conjecture
-- name    : jesmanowicz_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:12:14.815498+00:00
-- url     : https://prove2.me/theorems/d0276eee-2954-4f37-a203-3e8cd285ccd5
-- statement:
--   Jeśmanowicz conjecture (1956): If (a,b,c) is a primitive Pythagorean triple, then the only solution to a^x + b^y = c^z in positive integers is x=y=z=2. Proved for many specific triples. General case open.
-- source:
--   https://en.wikipedia.org/wiki/Je%C5%9Bmanowicz_conjecture

import Mathlib

import Mathlib

theorem jesmanowicz_conjecture (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2) (hcop : Nat.Coprime a b) :
    ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → 1 ≤ z →
      a ^ x + b ^ y = c ^ z → x = 2 ∧ y = 2 ∧ z = 2 := by
  sorry
