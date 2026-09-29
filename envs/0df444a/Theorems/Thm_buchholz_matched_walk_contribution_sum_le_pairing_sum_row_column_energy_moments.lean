-- Prove2me | Theorems.Thm_buchholz_matched_walk_contribution_sum_le_pairing_sum_row_column_energy_moments
-- name    : buchholz_matched_walk_contribution_sum_le_pairing_sum_row_column_energy_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T16:34:31.973177+00:00
-- url     : https://prove2.me/theorems/ad3c269e-b4ff-4313-ac52-fb8c501c6540
-- title:
--   Buchholz contribution sum bounded by pairing-summed row/column energy
-- statement:
--   This is the contribution-level form of Buchholz's matched-walk domination used in Candès--Recht Section 6.1.
--
--   For a fixed sampled matrix and integer $n \ge 1$, the total surviving matched-walk contribution is bounded by summing, once for each pair partition of the $2n$ edge-occurrence positions, the larger of the row and column diagonal energy moments:
--
--   $$
--   \sum_{\mathrm{rows}}\sum_{\mathrm{cols}} \mathrm{Contribution}(\Omega,p,X;\mathrm{rows},\mathrm{cols})
--   \le \sum_{\pi\in\mathcal P_2(2n)} \max(E_{\mathrm{row}},E_{\mathrm{col}}).
--   $$
--
--   This node isolates the genuine Buchholz combinatorial charging step before the elementary specialization to row-dominant or column-dominant cases.
-- source:
--   Buchholz, "Operator Khintchine inequality in non-commutative probability", Math. Ann. 319 (2001), Sections 2--3; used in Candès--Recht, "Exact Matrix Completion via Convex Optimization", Section 6.1, Lemma 6.1, PDF p. 25.

import Definitions.Def_buchholz_matched_walk_contribution
import Definitions.Def_buchholz_pairing

open MatrixCompletion
open scoped BigOperators

theorem buchholz_matched_walk_contribution_sum_le_pairing_sum_row_column_energy_moments
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    (∑ rows : Fin n → Fin n1,
      ∑ cols : Fin n → Fin n2,
        buchholzMatchedWalkContribution Omega p X rows cols)
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
