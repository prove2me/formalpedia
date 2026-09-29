-- Prove2me | solution 1 for buchholz_contribution_pairing_energy_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-26T14:45:12.178038+00:00
-- url     : https://prove2.me/submissions/7274822f-5853-4ff6-ac6b-b8de17150c46

import Theorems.Thm_buchholz_contribution_pairing_count_energy_domination

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; Candes--Recht,
Section 6.1, Lemma 6.1, PDF p. 25.

This reduction is a finite-sum wrapper around the cardinality form of the
Buchholz contribution estimate.  The imported child carries the mathematical
content: the total matched one-walk contribution is bounded by
`Fintype.card (BuchholzPairing n)` times the larger diagonal row/column energy
moment.  The parent statement writes the same right-hand side as a sum over all
pair partitions of that constant maximum.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    Finset.univ.sum (fun rows : Fin n → Fin n1 =>
      Finset.univ.sum (fun cols : Fin n → Fin n2 =>
        buchholzMatchedWalkContribution Omega p X rows cols))
      ≤ Finset.univ.sum (fun _pairing : BuchholzPairing n =>
          max
            (Finset.univ.sum (fun i : Fin n1 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
            (Finset.univ.sum (fun j : Fin n2 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))) := by
  simpa using
    buchholz_contribution_pairing_count_energy_domination n hn Omega p hp X
