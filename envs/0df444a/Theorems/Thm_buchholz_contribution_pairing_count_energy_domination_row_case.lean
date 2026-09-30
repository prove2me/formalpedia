-- Prove2me | Theorems.Thm_buchholz_contribution_pairing_count_energy_domination_row_case
-- name    : buchholz_contribution_pairing_count_energy_domination_row_case
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T14:53:32.134482+00:00
-- url     : https://prove2.me/theorems/91daad10-14fa-4a6d-9be4-6bd80384fda4
-- title:
--   Buchholz contribution pairing-count domination: row-energy case
-- statement:
--   This is the row-energy branch of the Buchholz matched-walk contribution estimate used in the noncommutative Khintchine bound.
--
--   Let $nge 1$, let $Omega$ be a sampled set of matrix coordinates, let $p>0$, and let $X$ be a real matrix. If the row diagonal energy moment is at least the column diagonal energy moment, then the total matched-walk contribution is bounded by the number of Buchholz pair partitions times the larger row/column energy maximum:
--
--   $$
--   sum_{	ext{rows}}sum_{	ext{cols}} C_{Omega,p,X}(	ext{rows},	ext{cols})
--   le |mathcal P_{2n}|,max(R_n,C_n).
--   $$
--
--   This isolates the row-dominant case of the combinatorial charging argument from the final linear-order case split.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candes--Recht, "Exact Matrix Completion via Convex Optimization", Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_matched_walk_contribution
import Definitions.Def_buchholz_pairing

open MatrixCompletion
open scoped BigOperators

theorem buchholz_contribution_pairing_count_energy_domination_row_case
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2)
    (hrow :
      (Finset.univ.sum (fun j : Fin n2 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
        ≤
      (Finset.univ.sum (fun i : Fin n1 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))) :
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
