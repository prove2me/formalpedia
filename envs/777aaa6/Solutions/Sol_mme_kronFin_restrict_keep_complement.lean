-- Prove2me | solution 1 for mme_kronFin_restrict_keep_complement
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:06:59.17609+00:00
-- url     : https://prove2.me/submissions/1b8c002c-8424-4ba5-821f-ddb8153f2822

import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_toQ_kronFin

open MME MME.TensorObj BigOperators
universe u

/-- Restrict the selected factors of a finite tensor product and retain every
complementary factor. Unselected entries of the extracted family are scalar
units, so no tensor factor is discarded. -/
theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (selected : Fin n → Prop) [DecidablePred selected]
    (P T : Fin n → TensorObj K d)
    (hselected : ∀ j, selected j → Restrict (P j) (T j))
    (hunit : ∀ j, ¬ selected j → Isomorphic (P j) oneObj) :
    Restrict
      (kron (kronFin n P)
        (kronFin n (fun j => if selected j then oneObj else T j)))
      (kronFin n T) := by
  let R := fun j => if selected j then oneObj else T j
  have hf (j : Fin n) : Restrict (kron (P j) (R j)) (T j) := by
    by_cases hj : selected j
    · have hi : Isomorphic (kron (P j) (R j)) (P j) := by
        rw [← TensorQ.toQ_eq_iff]
        simp only [R, if_pos hj, TensorQ.toQ_kron, ← TensorQ.toQ_one, mul_one]
      exact hi.1.trans (hselected j hj)
    · have hi : Isomorphic (kron (P j) (R j)) (T j) := by
        rw [← TensorQ.toQ_eq_iff]
        rw [TensorQ.toQ_kron, (TensorQ.toQ_eq_iff.mpr (hunit j hj))]
        simp only [R, if_neg hj, ← TensorQ.toQ_one, one_mul]
      exact hi.1
  have hr : Isomorphic (kron (kronFin n P) (kronFin n R))
      (kronFin n (fun j => kron (P j) (R j))) := by
    rw [← TensorQ.toQ_eq_iff]
    simp only [TensorQ.toQ_kron, mme_toQ_kronFin, Finset.prod_mul_distrib]
  exact hr.1.trans (mme_kronFin_mono_restrict hf)


#print axioms solution
