-- Prove2me | Theorems.Thm_gilbreath_conjecture
-- name    : gilbreath_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:49:46.084522+00:00
-- url     : https://prove2.me/theorems/f2391622-2430-42fd-9e5f-8e7868224741
-- statement:
--   **Gilbreath's Conjecture**: Form the sequence of primes 2, 3, 5, 7, 11, 13, ... and take successive rows of absolute differences:
--
--   Row 0: 2, 3, 5, 7, 11, 13, 17, 19, ...
--   Row 1: 1, 2, 2, 4, 2, 4, 2, ... (|p_{n+1} - p_n|)
--   Row 2: 1, 0, 2, 2, 2, 2, ... (absolute diffs of row 1)
--   Row 3: 1, 2, 0, 0, 0, ...
--
--   The conjecture: every row after row 0 begins with 1. Proposed by Norman Gilbreath (1958), verified computationally up to the first 10^13 primes by Odlyzko (1993). No proof exists.
--
--   **Source**: Odlyzko, A.M. (1993). Mathematics of Computation, 61(203), 373–380. DOI:10.1090/S0025-5718-1993-1192979-9
-- source:
--   https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Mathlib

noncomputable def gilbreathRow : ℕ → ℕ → ℕ
  | 0, k => Nat.nth Nat.Prime k
  | (n+1), k => Int.natAbs ((gilbreathRow n k : ℤ) - (gilbreathRow n (k+1) : ℤ))

theorem gilbreath_conjecture (n : ℕ) : gilbreathRow (n + 1) 0 = 1 := by
  sorry
