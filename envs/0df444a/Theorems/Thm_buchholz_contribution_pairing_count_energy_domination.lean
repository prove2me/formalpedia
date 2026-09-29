-- Prove2me | Theorems.Thm_buchholz_contribution_pairing_count_energy_domination
-- name    : buchholz_contribution_pairing_count_energy_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T14:45:11.357768+00:00
-- url     : https://prove2.me/theorems/523301dd-e7c9-43ad-9470-cc53f4fd34ed
-- title:
--   Buchholz contribution domination with pairing count
-- statement:
--   Let $nge 1$, let $Omegasubseteq[n_1]	imes[n_2]$, let $p>0$, and let $X$ be a real matrix.  The left side is the total one-walk contribution that remains after Rademacher sign averaging in Buchholz's even-moment expansion.
--
--   This theorem states that this total contribution is bounded by the number of pair partitions of the $2n$ edge positions times the larger of the row and column diagonal energy moments:
--
--   $$
--   sum_{rows,cols} mathrm{Contribution}(rows,cols)le |mathrm{Pair}(2n)|,max{R_n(Omega,p,X),C_n(Omega,p,X)}.
--   $$
--
--   It is the same Buchholz matched-walk domination used in the noncommutative Khintchine proof, kept in cardinality form so the surrounding theorem can separately rewrite $|mathrm{Pair}(2n)|,M$ as a constant sum over pairings.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candes--Recht, Exact Matrix Completion via Convex Optimization, Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_matched_walk_contribution
import Definitions.Def_buchholz_pairing
open MatrixCompletion
open scoped BigOperators

theorem buchholz_contribution_pairing_count_energy_domination
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    Finset.univ.sum (fun rows : Fin n → Fin n1 =>
      Finset.univ.sum (fun cols : Fin n → Fin n2 =>
        buchholzMatchedWalkContribution Omega p X rows cols))
      ≤ (Fintype.card (BuchholzPairing n) : ℝ) *
          max
            (Finset.univ.sum (fun i : Fin n1 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
            (Finset.univ.sum (fun j : Fin n2 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n)) := by
  sorry
