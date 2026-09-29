-- Prove2me | Theorems.Thm_mme_MMObj_power_third_word_basis_maps
-- name    : mme_MMObj_power_third_word_basis_maps
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T03:25:50.085872+00:00
-- url     : https://prove2.me/theorems/2331cb75-8890-4541-8c0f-9848f94ff67a
-- title:
--   Matrix tensor powers preserve separate row and column word labels
-- statement:
--   For every field K, natural dimensions n, m, p and exponent N, there are mode-wise linear maps from the Nth Kronecker power of the matrix multiplication tensor of dimensions (n,m,p) to the matrix multiplication tensor of dimensions (n^N,m^N,p^N), carrying the source tensor to the target tensor. There are also separate equivalences from length-N row words to Fin(p^N) and column words to Fin(n^N). On each third-coordinate word basis vector, the third mode map is the singleton at the corresponding row-word and column-word indices. The statement includes N=0 and zero matrix dimensions. This specifies the basis action needed to transport Cartesian row and column selections through matrix-power flattening.
-- source:
--   Induction using the canonical matrix Kronecker equivalence and its third-coordinate singleton formula.

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_MMObj_power_third_word_basis_maps
    {K : Type u} [Field K] (n m p N : ℕ) :
    let T := MMObj K n m p
    let b := (Pi.basisFun K (Fin p × Fin n)).reindex Equiv.ulift.symm
    ∃ (f : ∀ i, (T.kronPow N).V i →ₗ[K] (MMObj K (n^N) (m^N) (p^N)).V i)
      (rows : PowIndex (ULift.{u} (Fin p)) N ≃ Fin (p^N))
      (cols : PowIndex (ULift.{u} (Fin n)) N ≃ Fin (n^N)),
      PiTensorProduct.map f (T.kronPow N).t = (MMObj K (n^N) (m^N) (p^N)).t ∧
      ∀ w : PowIndex (ULift.{u} (Fin p × Fin n)) N,
        f 2 (kronPowModeBasis T 2 b N w) =
          Pi.single
            (rows (PowIndex.ofFun N (fun r ↦ ⟨(PowIndex.get N w r).down.1⟩)),
             cols (PowIndex.ofFun N (fun r ↦ ⟨(PowIndex.get N w r).down.2⟩))) 1 := by sorry
