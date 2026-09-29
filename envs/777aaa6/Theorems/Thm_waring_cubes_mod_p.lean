-- Prove2me | Theorems.Thm_waring_cubes_mod_p
-- name    : waring_cubes_mod_p
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:55:37.884982+00:00
-- url     : https://prove2.me/theorems/8a8fa4d7-1042-41f8-b3cc-8de89b65a384
-- statement:
--   Waring's problem mod p (for cubes): Every element of ℤ/pℤ is a sum of g cubes. For p ≡ 1 (mod 3), g = 5 is conjectured. Best known bounds involve character sum estimates. Exact g(3, p) for specific primes is open.
-- source:
--   https://en.wikipedia.org/wiki/Waring%27s_problem

import Mathlib

import Mathlib

theorem waring_cubes_mod_p (p : ℕ) (hp : Nat.Prime p) (h3 : 3 ∣ p - 1) :
    ∃ (g : ℕ) (_ : g ≤ 5), ∀ n : ZMod p,
      ∃ (xs : Fin g → ZMod p), n = ∑ i, xs i ^ 3 := by
  sorry
