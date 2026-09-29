-- Prove2me | solution 1 for mme_cyclic_oriented_power_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:02:02.849317+00:00
-- url     : https://prove2.me/submissions/ddbee1ac-dbb5-406b-bf6f-10ceee38471d

import Theorems.Thm_mme_permutation_kronPow_eq

open MME PiTensorProduct
universe u
set_option autoImplicit false

private theorem perm_trans_eq {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.permObj e' (TensorObj.permObj e X) =
      TensorObj.permObj (e.trans e') X := by
  unfold TensorObj.permObj
  congr 1
  exact reindex_reindex e e' X.t

private theorem perm_refl_eq {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) : TensorObj.permObj (Equiv.refl _) X = X := by
  cases X
  simp only [TensorObj.permObj, reindex_refl]
  rfl

/-- The two oriented half-powers return to the original tensor power under
opposite cyclic rotations, with equality of the tensor objects. -/
theorem solution {K : Type u} [Field K]
    (X : TensorObj K 3) (n : ℕ) :
    TensorObj.permObj cyclicPerm
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) X).kronPow n) =
        X.kronPow n ∧
      TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        ((TensorObj.permObj cyclicPerm X).kronPow n) = X.kronPow n := by
  have h₁ : (cyclicPerm.trans cyclicPerm).trans cyclicPerm = Equiv.refl _ := by
    ext i
    fin_cases i <;> rfl
  have h₂ : cyclicPerm.trans (cyclicPerm.trans cyclicPerm) = Equiv.refl _ := by
    ext i
    fin_cases i <;> rfl
  constructor
  · rw [mme_permutation_kronPow_eq, perm_trans_eq, h₁, perm_refl_eq]
  · rw [mme_permutation_kronPow_eq, perm_trans_eq, h₂, perm_refl_eq]

#print axioms solution
