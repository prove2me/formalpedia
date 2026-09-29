-- Prove2me | solution 1 for mme_little_endian_MM_kronPow_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:21:16.401372+00:00
-- url     : https://prove2.me/submissions/4139a7b1-7037-4397-82ec-364ff1d3832e

import Definitions.Def_mme_little_endian_MM_power_flatten
import Theorems.Thm_mme_little_endian_MM_kron_tensor

open PiTensorProduct TensorProduct BigOperators
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem solution
    (K : Type u) [Field K] (n m p r : ℕ) :
    PiTensorProduct.map (littleEndianPowerMaps K n m p r)
        ((MMObj K n m p).kronPow r).t =
      (MMObj K (n ^ r) (m ^ r) (p ^ r)).t := by
  induction r with
  | zero =>
      rw [littleEndianPowerMaps_zero]
      change PiTensorProduct.map (littleEndianUnitMaps K)
          (PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))) =
        (MMObj K 1 1 1).t
      rw [PiTensorProduct.map_tprod, littleEndianMMObj_t_eq]
      simp only [Fin.sum_univ_one]
      unfold littleEndianMMPure
      congr 1
      funext s
      fin_cases s <;> funext ab <;>
        rw [show ab = ((0 : Fin 1), (0 : Fin 1)) from
          Subsingleton.elim _ _] <;>
        simp [littleEndianUnitMaps, singletonPairMap]
  | succ r ih =>
      rw [littleEndianPowerMaps_succ]
      change PiTensorProduct.map
          (fun s =>
            (littleEndianModeEquiv K n m p (n ^ r) (m ^ r) (p ^ r) s).toLinearMap ∘ₗ
              TensorProduct.map LinearMap.id
                (littleEndianPowerMaps K n m p r s))
          (interchange (MMObj K n m p).t
            ((MMObj K n m p).kronPow r).t) =
        (MMObj K ((n ^ r) * n) ((m ^ r) * m) ((p ^ r) * p)).t
      rw [PiTensorProduct.map_comp]
      change PiTensorProduct.map
          (fun s =>
            (littleEndianModeEquiv K n m p (n ^ r) (m ^ r) (p ^ r) s).toLinearMap)
          (PiTensorProduct.map
            (fun s => TensorProduct.map LinearMap.id
              (littleEndianPowerMaps K n m p r s))
            (interchange (MMObj K n m p).t
              ((MMObj K n m p).kronPow r).t)) = _
      rw [TensorObj.TypeGrading.kronMap_interchange,
        PiTensorProduct.map_id, ih]
      exact mme_little_endian_MM_kron_tensor K
        n m p (n ^ r) (m ^ r) (p ^ r)
