-- Prove2me | Theorems.Thm_infinitely_many_amicable
-- name    : infinitely_many_amicable
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:30:59.075888+00:00
-- url     : https://prove2.me/theorems/5bc951fd-5bf9-4a2d-942a-e36777283aae
-- statement:
--   Infinitely many amicable pairs: Are there infinitely many pairs (m,n) where σ(m)=m+n and σ(n)=m+n? The 276 pairs known suggest yes. No proof of infinitude. Also open: do all amicable pairs have even sum?
-- source:
--   https://en.wikipedia.org/wiki/Amicable_numbers

import Mathlib

import Mathlib

theorem infinitely_many_amicable :
    {n : ℕ | ∃ m : ℕ, m ≠ n ∧
      (n.divisors.sum id - n) = m ∧
      (m.divisors.sum id - m) = n}.Infinite := by
  sorry
