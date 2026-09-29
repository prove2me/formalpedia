-- Prove2me | solution 1 for buchholz_signed_walk_sum_expectation_eq_matched_walk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T23:14:39.611728+00:00
-- url     : https://prove2.me/submissions/b707047e-8178-44c2-a7fa-0741c31cead9

import Theorems.Thm_buchholz_signed_walk_term_expectation_eq_matched_indicator

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Section 2; Candès--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

Reduction: apply the one-walk Rademacher orthogonality lemma to each
row/column closed walk and commute the finite sign and walk sums.
-/
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps => buchholzSignedWalkSum n Omega p X eps)
      = buchholzMatchedWalkSum n Omega p X := by
  classical
  unfold rademacherExpectation buchholzSignedWalkSum buchholzMatchedWalkSum
  calc
    ∑ eps : Finset (Fin n1 × Fin n2),
        rademacherObservationWeight eps *
          (∑ rows : Fin n → Fin n1,
            ∑ cols : Fin n → Fin n2,
              buchholzSignedWalkTerm Omega eps p X rows cols)
        =
      ∑ rows : Fin n → Fin n1,
        ∑ cols : Fin n → Fin n2,
          ∑ eps : Finset (Fin n1 × Fin n2),
            rademacherObservationWeight eps *
              buchholzSignedWalkTerm Omega eps p X rows cols := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro rows _hrows
        rw [Finset.sum_comm]
    _ =
      ∑ rows : Fin n → Fin n1,
        ∑ cols : Fin n → Fin n2,
          rademacherExpectation
            (fun eps => buchholzSignedWalkTerm Omega eps p X rows cols) := by
        rfl
    _ =
      ∑ rows : Fin n → Fin n1,
        ∑ cols : Fin n → Fin n2,
          buchholzMatchedWalkContribution Omega p X rows cols := by
        simp [buchholz_signed_walk_term_expectation_eq_matched_indicator]
    _ = ∑ rows : Fin n → Fin n1,
        ∑ cols : Fin n → Fin n2,
          if buchholzWalkMatched rows cols then
            buchholzWalkProduct Omega p X rows cols
          else
            0 := by
        rfl
