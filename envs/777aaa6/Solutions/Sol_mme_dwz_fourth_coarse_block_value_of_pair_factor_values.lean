-- Prove2me | solution 1 for mme_dwz_fourth_coarse_block_value_of_pair_factor_values
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:24:02.842542+00:00
-- url     : https://prove2.me/submissions/35237d34-731d-49ef-b6bc-78badf7f9499

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_dwz_fourth_pair_factor_restrictions_to_coarse
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kron_of_each_strict_below_product

open MME BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (q : ℕ) (p : Fin 15 × Fin 15)
    (sigma : Fin 3 → Fin 9)
    (hx : (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val = (sigma 0).val)
    (hy : (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val = (sigma 1).val)
    (hz : (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val = (sigma 2).val)
    {X Y : TensorObj K 3}
    (hX : TensorObj.Restrict X
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1))))
    (hY : TensorObj.Restrict Y
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2))))
    (tau eX eY : ℝ) (heX : 0 < eX) (heY : 0 < eY)
    (hXv : ∀ V : ℝ, 0 ≤ V → V < eX → HasTauValueAtLeast X tau V)
    (hYv : ∀ V : ℝ, 0 ≤ V → V < eY → HasTauValueAtLeast Y tau V) :
    ∀ W : ℝ, 0 ≤ W → W < eX * eY →
      HasTauValueAtLeast
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor sigma)
        tau W := by
  intro W hW hWlt
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_dwz_fourth_pair_factor_restrictions_to_coarse q p sigma hx hy hz hX hY)
    (mme_HasTauValueAtLeast_kron_of_each_strict_below_product X Y tau eX eY
      heX heY hXv hYv W hW hWlt)
