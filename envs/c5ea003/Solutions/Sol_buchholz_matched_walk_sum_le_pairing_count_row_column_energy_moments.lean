-- Prove2me | solution 1 for buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-21T02:21:29.742882+00:00
-- url     : https://prove2.me/submissions/77574461-c1db-4725-a7d4-50b322d53454

import Theorems.Thm_buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; Candes--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

This reduction separates the real Buchholz matched-walk domination from the
finite counting wrapper.  The imported child says that the matched-walk sum is
bounded by summing one copy of the row/column energy maximum over all pair
partitions.  This parent sketch only rewrites that constant finite sum as
`Fintype.card (BuchholzPairing n)` times the same maximum.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ (Fintype.card (BuchholzPairing n) : ℝ) *
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  simpa using
    buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments
      n hn Omega p hp X
