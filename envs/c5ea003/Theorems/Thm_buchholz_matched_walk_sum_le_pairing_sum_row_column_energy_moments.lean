-- Prove2me | Theorems.Thm_buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments
-- name    : buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-21T02:21:02.701203+00:00
-- url     : https://prove2.me/theorems/34cfd85c-ca20-4a4e-a9a5-c0c3bb022e9b
-- statement:
--   For each pair partition of the $2n$ edge-occurrence positions in Buchholz's matched-walk expansion, the surviving closed-walk contribution is charged to one copy of the larger diagonal row/column energy moment. Equivalently, $W_n(\Omega,p,X)$ is bounded by the sum over all pairings of $\max\{R_n(\Omega,p,X),C_n(\Omega,p,X)\}$. This isolates Buchholz's pairing domination from the separate finite-counting wrapper.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candès--Recht, Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_pairing
open MatrixCompletion
open scoped BigOperators

theorem buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ∑ _pairing : BuchholzPairing n,
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by sorry
