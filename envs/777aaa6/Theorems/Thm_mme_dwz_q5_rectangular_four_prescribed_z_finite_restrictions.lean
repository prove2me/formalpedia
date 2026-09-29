-- Prove2me | Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions
-- name    : mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T09:25:49.428808+00:00
-- url     : https://prove2.me/theorems/d95f3fa3-87d6-4849-ba28-3acae6f694da
-- title:
--   Four q=5 elementary canonical components retain exact prescribed-Z matrix tensors
-- statement:
--   Let $K$ be a field and $p=(p_0,p_1,p_2;d)$ an integer fine-$Z$ profile. For $c\in\{1,3\}$, let $D_c$ count length-$dm$ words in the canonical coarse-grade-$c$ $Z$ basis with exactly $mp_a$ letters of left fine grade $a$. For every $m\in\mathbb N$, the actual canonical $q=5$ CW-square components satisfy
--   \[\langle1,1,D_3\rangle_K\preceq T_{013}^{\otimes dm}[p],\qquad \langle1,1,D_1\rangle_K\preceq T_{031}^{\otimes dm}[p],\]
--   \[\langle D_3,1,1\rangle_K\preceq T_{103}^{\otimes dm}[p],\qquad \langle D_1,1,1\rangle_K\preceq T_{301}^{\otimes dm}[p].\]
--   Every projection uses the literal canonical $Z$ basis and left fine grade. No profile or source tensor is replaced.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Section 7.3 after Lemma 7.14: a prescribed-Z projection of an elementary boundary component remains a rectangular matrix-multiplication tensor, with dimension equal to the surviving Z-variable count. This finite oriented q=5 specialization uses the accepted exact-Z routers.

import Theorems.Thm_mme_dwz_q5_rectangular_four_exact_z_basis_routers
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME Module MME.DWZComponentRestriction MME.DWZRestrictedValue
universe u
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions (K : Type u) [Field K] (p : IntegerZSplitProfile 3) (m : ℕ) :
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
        LiftedCoarsePair.leftGrade p m) := by sorry
