-- Prove2me | solution 1 for mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T09:27:31.155386+00:00
-- url     : https://prove2.me/submissions/262acc12-5abc-49f9-a55c-c242fbc17fc8

import Theorems.Thm_mme_dwz_q5_rectangular_four_exact_z_basis_routers
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME Module MME.DWZComponentRestriction MME.DWZRestrictedValue
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

theorem solution (K : Type u) [Field K] (p : IntegerZSplitProfile 3) (m : ℕ) :
    let D1 := Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 1) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w}
    let D3 := Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 3) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w}
    TensorObj.Restrict (MMObj K 1 1 D3)
      (prescribedZPower ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p m) ∧
    TensorObj.Restrict (MMObj K 1 1 D1)
      (prescribedZPower ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p m) ∧
    TensorObj.Restrict (MMObj K D3 1 1)
      (prescribedZPower ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p m) ∧
    TensorObj.Restrict (MMObj K D1 1 1)
      (prescribedZPower ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p m) := by
  classical
  dsimp only
  obtain ⟨h013, h031, h103, h301⟩ := mme_dwz_q5_rectangular_four_exact_z_basis_routers K
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨maps, htensor, coord, hZ⟩ := h013
    exact mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
      (T := (cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      (p.length m) (prescribedZWord LiftedCoarsePair.leftGrade p m)
      coord maps htensor hZ
  · obtain ⟨maps, htensor, coord, hZ⟩ := h031
    exact mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
      (T := (cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      (p.length m) (prescribedZWord LiftedCoarsePair.leftGrade p m)
      coord maps htensor hZ
  · obtain ⟨maps, htensor, coord, hZ⟩ := h103
    exact mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
      (T := (cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      (p.length m) (prescribedZWord LiftedCoarsePair.leftGrade p m)
      coord maps htensor hZ
  · obtain ⟨maps, htensor, coord, hZ⟩ := h301
    exact mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
      (T := (cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      (p.length m) (prescribedZWord LiftedCoarsePair.leftGrade p m)
      coord maps htensor hZ
