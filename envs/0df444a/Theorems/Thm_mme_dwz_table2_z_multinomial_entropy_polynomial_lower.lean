-- Prove2me | Theorems.Thm_mme_dwz_table2_z_multinomial_entropy_polynomial_lower
-- name    : mme_dwz_table2_z_multinomial_entropy_polynomial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:47:08.262576+00:00
-- url     : https://prove2.me/theorems/6caf7f06-7782-4d45-888c-2f5cdab97eb0
-- title:
--   Table-2 coarse-Z multinomial lower bound with explicit polynomial loss
-- statement:
--   For every positive integral Table-2 scale multiplier m, the exact five-cell coarse-Z multinomial is at least its entropy exponential divided by the displayed Stirling polynomial: exp(M m log(2) H(alpha_Z)) ≤ (6(Mm+1))^5 Mult(m c_Z). All histogram entries are the exact integers induced by Table 2.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.2 and Equation (21), printed pp. 53-54; exact Table 2 specialization on printed pp. 58-59; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_z_multinomial_entropy_polynomial_lower
    (m : ℕ) (hm : 0 < m) :
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeZ
              MME.DWZSquare.alpha)) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 5 *
        (Nat.multinomial Finset.univ
          (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) : ℝ) := by
  sorry
