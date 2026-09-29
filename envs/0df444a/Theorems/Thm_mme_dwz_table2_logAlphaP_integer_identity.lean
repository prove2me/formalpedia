-- Prove2me | Theorems.Thm_mme_dwz_table2_logAlphaP_integer_identity
-- name    : mme_dwz_table2_logAlphaP_integer_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T12:17:24.04574+00:00
-- url     : https://prove2.me/theorems/afbe192e-1e91-456e-8cf1-8386e73d1b5b
-- title:
--   DWZ Lemma 6.7: exact Table 2 integer entropy identity
-- statement:
--   Let S = 10^16 and use the exact integral Table 2 histograms for the typical-pair distribution gamma, its coarse Z marginal alpha_Z, each boundary-component split, and each interior (+,+,k) split. Then S times the compatibility exponent log_2(alpha_P) from DWZ Lemma 6.7 is exactly the sum of: S H(alpha_Z), minus S H(gamma), the component-count-weighted entropies of every boundary split, and the interior-mass-weighted entropies of every (+,+,k) split. Every entropy uses the corresponding normalized integral histogram. Zero-mass interior rows contribute zero. This identity is the precise arithmetic interface that lets finite multinomial estimates collect into the compatibility rate alpha_P in Equation (23); it contains no asymptotic approximation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4, Lemma 6.7 and Equation (23) (printed pp. 54-56 / PDF pp. 55-57), specialized to Section 6.3 Table 2.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_logAlphaP_integer_identity :
    (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.logAlphaP =
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_entropyBits
            (fun k ↦ (MME.DWZTable2Counts.alphaZ k : ℝ) /
              MME.DWZTable2Counts.scale) -
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_entropyBits
            (fun p ↦ (MME.DWZTable2Counts.gamma p : ℝ) /
              MME.DWZTable2Counts.scale) +
      (∑ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          (MME.DWZTable2Counts.component s : ℝ) *
            mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                MME.DWZTable2Counts.component s)
        else 0) +
      ∑ k : Fin 5,
        (MME.DWZTable2Counts.plusMass k : ℝ) *
          mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
              MME.DWZTable2Counts.plusMass k) := by
  sorry
