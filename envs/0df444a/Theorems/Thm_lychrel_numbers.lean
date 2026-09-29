-- Prove2me | Theorems.Thm_lychrel_numbers
-- name    : lychrel_numbers
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:06:17.502695+00:00
-- url     : https://prove2.me/theorems/822f9b5b-0770-4dbe-9c8b-6437babcb0b5
-- statement:
--   Lychrel number conjecture: Some natural numbers never become palindromes under the 'reverse and add' operation (196 is the most famous candidate). No proof exists that any Lychrel number is not eventually a palindrome; the reverse is also not proved.
-- source:
--   https://en.wikipedia.org/wiki/Lychrel_number

import Mathlib

import Mathlib

theorem lychrel_numbers :
    ∃ n : ℕ, ∀ k : ℕ,
      ¬∃ digits : List ℕ,
        (∀ d ∈ digits, d < 10) ∧
        Nat.rec n (fun _ m =>
          let rev := (Nat.digits 10 m).reverse
          m + rev.foldl (fun acc d => 10 * acc + d) 0) k =
        digits.foldl (fun acc d => 10 * acc + d) 0 ∧
        digits = digits.reverse := by
  sorry
