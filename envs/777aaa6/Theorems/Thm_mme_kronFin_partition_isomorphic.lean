-- Prove2me | Theorems.Thm_mme_kronFin_partition_isomorphic
-- name    : mme_kronFin_partition_isomorphic
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:00:14.739606+00:00
-- url     : https://prove2.me/theorems/af751d44-7b3b-4c8e-8683-1ed06ed0925f
-- title:
--   A finite tensor partition gives two indexed subproducts
-- statement:
--   An equivalence partitioning the finite factor index gives an actual tensor isomorphism to the Kronecker product of the two subproducts. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_toQ_kronFin
open MME BigOperators
universe u

theorem mme_kronFin_partition_isomorphic {K : Type u} [Field K] {a b : ℕ}
    (e : (Fin a ⊕ Fin b) ≃ Fin (a + b)) (T : Fin (a + b) → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kronFin (a + b) T)
      (TensorObj.kron
        (TensorObj.kronFin a (fun i ↦ T (e (.inl i))))
        (TensorObj.kronFin b (fun i ↦ T (e (.inr i))))) := by sorry
