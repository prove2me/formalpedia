-- Prove2me | Theorems.Thm_buchholz_contribution_pairing_count_column_energy_bound
-- name    : buchholz_contribution_pairing_count_column_energy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T15:28:49.397214+00:00
-- url     : https://prove2.me/theorems/b36ced2e-22f0-44b2-9ea6-5831521b34e2
-- title:
--   Buchholz pairing-count domination by column energy
-- statement:
--   This is the column-energy form of the Buchholz matched-walk contribution estimate used in the noncommutative Khintchine inequality.
--
--   Let $nge 1$, let $\Omega$ be a finite set of sampled matrix coordinates, let $p>0$, and let $X$ be a real matrix. Assume the column diagonal energy moment dominates the row diagonal energy moment. Then the sum of all surviving sign-averaged matched-walk contributions is bounded by the number of pair partitions of $2n$ positions times the column energy moment.
--
--   This is the substantive column-dominant Buchholz charging estimate below the existing max-wrapper theorem. It is designed to be reused by the wrapper that rewrites $\max(R_n,C_n)$ to the dominant side.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candes--Recht, "Exact Matrix Completion via Convex Optimization", Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_matched_walk_contribution
import Definitions.Def_buchholz_pairing

open MatrixCompletion
open scoped BigOperators

theorem buchholz_contribution_pairing_count_column_energy_bound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2)
    (hcol :
      (Finset.univ.sum (fun i : Fin n1 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
        ≤
      (Finset.univ.sum (fun j : Fin n2 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))) :
    Finset.univ.sum (fun rows : Fin n → Fin n1 =>
      Finset.univ.sum (fun cols : Fin n → Fin n2 =>
        buchholzMatchedWalkContribution Omega p X rows cols))
      ≤ (Fintype.card (BuchholzPairing n) : ℝ) *
          (Finset.univ.sum (fun j : Fin n2 =>
            (p⁻¹ ^ 2 *
              (Finset.univ.sum
                (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n)) := by
  sorry
