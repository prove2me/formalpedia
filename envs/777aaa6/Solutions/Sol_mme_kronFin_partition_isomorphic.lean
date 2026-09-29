-- Prove2me | solution 1 for mme_kronFin_partition_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:01:54.878742+00:00
-- url     : https://prove2.me/submissions/63f83220-c4e0-40c4-a759-ac508d06eb1a

import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators
universe u
set_option autoImplicit false

/-- A partition of the finite factor index gives an actual tensor
isomorphism to the Kronecker product of the two indexed subproducts. -/
theorem solution {K : Type u} [Field K] {a b : ℕ}
    (e : (Fin a ⊕ Fin b) ≃ Fin (a + b)) (T : Fin (a + b) → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kronFin (a + b) T)
      (TensorObj.kron
        (TensorObj.kronFin a (fun i ↦ T (e (.inl i))))
        (TensorObj.kronFin b (fun i ↦ T (e (.inr i))))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [TensorQ.toQ_kron, mme_toQ_kronFin]
  rw [← Equiv.prod_comp e (fun i ↦ TensorQ.toQ (T i)), Fintype.prod_sum_type]


#print axioms solution
