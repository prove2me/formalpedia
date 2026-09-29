-- Prove2me | solution 1 for mme_kronFin_repeated_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:07.314343+00:00
-- url     : https://prove2.me/submissions/983ef5ee-7848-466d-b83e-e19390175c73

import Theorems.Thm_mme_toQ_kronFin

open MME MME.TensorObj BigOperators
universe u

/-- Independent multiplicities in a finite tensor product multiply exactly,
including zero copies and the empty product. -/
theorem solution {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (copies : Fin n → ℕ) :
    Isomorphic (kronFin n (fun r => bigAdd (fun _ : Fin (copies r) => T r)))
      (bigAdd (fun _ : Fin (∏ r, copies r) => kronFin n T)) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [mme_toQ_kronFin, TensorQ.toQ_bigAdd, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.prod_mul_distrib,
    Nat.cast_prod]


#print axioms solution
