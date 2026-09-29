-- Prove2me | Theorems.Thm_buchholz_contribution_pairing_energy_domination
-- name    : buchholz_contribution_pairing_energy_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-22T15:13:32.28403+00:00
-- url     : https://prove2.me/theorems/362b532c-9a77-4217-83bb-54abc6910b1a
-- title:
--   Buchholz contribution pairing-energy domination
-- statement:
--   Explicit one-walk contribution form of Buchholz's matched-walk domination. The sum of `buchholzMatchedWalkContribution` over row/column closed walks is bounded by summing one copy of the larger row/column diagonal energy moment over all pair partitions of the $2n$ edge positions. Source-backed by Buchholz, Math. Ann. 319 (2001), Sections 2--3, as used in Candes--Recht Section 6.1 Lemma 6.1.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_matched_walk_contribution
import Definitions.Def_buchholz_pairing
open MatrixCompletion
open scoped BigOperators

theorem buchholz_contribution_pairing_energy_domination
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
  sorry
