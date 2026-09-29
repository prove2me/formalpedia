-- Prove2me | solution 1 for mme_permutation_kronPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:00:05.962985+00:00
-- url     : https://prove2.me/submissions/297346c7-e4c3-4e35-ad44-9d45ac8fc6c0

import Definitions.Def_mme_permutation

open MME PiTensorProduct
universe u
set_option autoImplicit false

private theorem perm_kron_eq {K : Type u} [Field K] {d : ℕ}
    (e : Equiv.Perm (Fin d)) (X Y : TensorObj K d) :
    TensorObj.permObj e (X.kron Y) =
      (TensorObj.permObj e X).kron (TensorObj.permObj e Y) := by
  unfold TensorObj.permObj TensorObj.kron
  simp only [reindex_interchange]

/-- Permuting the modes commutes with taking a Kronecker power as an equality
of tensor objects, preserving the original mode coordinates. -/
theorem solution {K : Type u} [Field K] {d : ℕ}
    (e : Equiv.Perm (Fin d)) (X : TensorObj K d) (n : ℕ) :
    TensorObj.permObj e (X.kronPow n) = (TensorObj.permObj e X).kronPow n := by
  induction n with
  | zero =>
      have ht : (reindex K (fun _ : Fin d => K) e)
          (tprod K (fun _ => (1 : K))) = tprod K (fun _ => (1 : K)) := by
        rw [reindex_tprod]
      unfold TensorObj.kronPow TensorObj.permObj TensorObj.oneObj
      rw [ht]
  | succ n ih =>
      change TensorObj.permObj e (X.kron (X.kronPow n)) =
        (TensorObj.permObj e X).kron ((TensorObj.permObj e X).kronPow n)
      rw [perm_kron_eq, ih]

#print axioms solution
