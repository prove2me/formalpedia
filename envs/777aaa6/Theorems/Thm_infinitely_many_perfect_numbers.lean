-- Prove2me | Theorems.Thm_infinitely_many_perfect_numbers
-- name    : infinitely_many_perfect_numbers
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:47:31.168089+00:00
-- url     : https://prove2.me/theorems/8195a2d2-411c-4723-aab2-f5364e682777
-- statement:
--   Are there infinitely many perfect numbers? All known perfect numbers are even and of the form 2^(p-1)(2^p-1) where 2^p-1 is a Mersenne prime. This is infinite iff there are infinitely many Mersenne primes (unknown). The question of infinitely many even perfect numbers is equivalent to the Mersenne prime infinitude conjecture.
-- source:
--   https://en.wikipedia.org/wiki/Perfect_number

import Mathlib

import Mathlib

theorem infinitely_many_perfect_numbers :
    {n : ℕ | n.divisors.sum id = 2 * n}.Infinite := by
  sorry
