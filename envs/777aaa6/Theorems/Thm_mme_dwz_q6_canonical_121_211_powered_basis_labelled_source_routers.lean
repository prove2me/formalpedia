-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
-- name    : mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:59:04.703715+00:00
-- url     : https://prove2.me/theorems/58de556c-f9eb-4825-98bb-cd34aa32e93f
-- title:
--   Powered exact basis-labelled routers for q=6 rows 121 and 211
-- statement:
--   For every power length $n$, the two exact canonical q=6 source routers lift positionwise to the $n$-fold Kronecker powers of Table-2 rows 121 and 211.  The lifted maps preserve the distinguished tensors exactly.  On the recursive Z-word basis they apply the same explicit decoder in every position: the two six-element fine-coordinate families are retained, and their left split grades remain respectively 0 and 1.  This is the powered source interface needed to transport the literal prescribed-word projectors into the two complementary coupled modes before asymmetric hashing.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and Section 6.3; standard functoriality of Kronecker powers.

import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_permutation

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
    (K : Type u) [Field K] (n : ℕ) :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) ∧
      (∃ maps : ∀ i : Fin 3,
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).V i →ₗ[K]
            ((TensorObj.permObj cyclicPerm
              (coupledObj K 6)).kronPow n).V i,
        PiTensorProduct.map maps
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).t =
          ((TensorObj.permObj cyclicPerm
            (coupledObj K 6)).kronPow n).t ∧
        ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
          maps 2
              (kronPowModeBasis
                (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) n w) =
            kronPowModeBasis
              (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
              ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                Equiv.ulift.symm) n
              (PowIndex.ofFun n
                (fun r ↦ ULift.up (coord (PowIndex.get n w r))))) := by
  sorry
