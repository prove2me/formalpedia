-- Prove2me | Theorems.Thm_buchholz_pairing_count_eq_factorial_ratio
-- name    : buchholz_pairing_count_eq_factorial_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T03:01:36.2156+00:00
-- url     : https://prove2.me/theorems/f6a105fc-50af-46c7-9e87-4f93c61ad1a5
-- statement:
--   The number of pair partitions of $2n$ labelled positions is
--   $$
--   |\mathrm{Pair}(2n)|=\frac{(2n)!}{2^n n!}.
--   $$
--   In the Lean statement, pair partitions are represented as fixed-point-free involutions on `Fin (2 * n)`. This theorem is the standard enumeration: order the $2n$ labels, divide by $2$ for the order inside each pair, and divide by $n!$ for the order of the pairs.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_pairing
open MatrixCompletion

theorem buchholz_pairing_count_eq_factorial_ratio (n : Nat) :
    (Fintype.card (BuchholzPairing n) : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) := by
  sorry
