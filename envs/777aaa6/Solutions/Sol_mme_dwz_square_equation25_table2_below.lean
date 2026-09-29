-- Prove2me | solution 1 for mme_dwz_square_equation25_table2_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:47:20.234174+00:00
-- url     : https://prove2.me/submissions/c6def79c-a463-4ab0-8f49-699715d4d968

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_square_equation25_cofinal_finite_extraction
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < squareRate tau) :
    HasSixSymmetricTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V := by
  unfold HasSixSymmetricTauValueAtLeast
  obtain ⟨s, loss, hs, hloss, hextract⟩ :=
    mme_dwz_square_equation25_cofinal_finite_extraction
      (K := K) tau htau V hV hVlt
  exact mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (sixSymmetrization (TensorObj.kron (CWObj K 6) (CWObj K 6)))
    tau (V ^ (6 : ℕ)) (pow_nonneg hV 6)
    s hs loss hloss hextract
