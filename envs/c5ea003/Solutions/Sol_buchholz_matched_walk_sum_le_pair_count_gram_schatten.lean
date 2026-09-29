-- Prove2me | solution 1 for buchholz_matched_walk_sum_le_pair_count_gram_schatten
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T01:55:22.353673+00:00
-- url     : https://prove2.me/submissions/799e11bd-32c5-4a53-9a07-a860ac55a78e

import Theorems.Thm_buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
import Theorems.Thm_sampled_row_gram_schatten_even_power_eq_row_energy_moment
import Theorems.Thm_sampled_column_gram_schatten_even_power_eq_column_energy_moment

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3, gives the matched-walk
pair-count estimate in terms of the two Gram moment traces.  Candes--Recht
Section 6.1, Lemma 6.1, PDF p. 25 specializes those Gram traces to the sampled
coordinate matrices, where they are the row and column sampled energy moments.

This sketch is the formal bridge from the explicit row/column energy version of
the Buchholz estimate to the local `sampledRowGramSchatten` and
`sampledColumnGramSchatten` vocabulary.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  rw [sampled_row_gram_schatten_even_power_eq_row_energy_moment n hn Omega p hp X]
  rw [sampled_column_gram_schatten_even_power_eq_column_energy_moment n hn Omega p hp X]
  exact
    buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
      n hn Omega p hp X
