-- Prove2me | Theorems.Thm_mme_dwz_table2_component_multinomial_entropy_polynomial_lower
-- name    : mme_dwz_table2_component_multinomial_entropy_polynomial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:47:22.375787+00:00
-- url     : https://prove2.me/theorems/d5f050b4-fe05-4713-b241-6ef2f349dfa3
-- title:
--   Table-2 joint multinomial lower bound with explicit polynomial loss
-- statement:
--   For every positive integral Table-2 scale multiplier m, the exact fifteen-cell joint-type multinomial is at least its entropy exponential divided by the displayed Stirling polynomial: exp(M m log(2) H(alpha)) ≤ (6(Mm+1))^15 Mult(m c). Here M = 10^16 and c_s = M alpha_s are the exact Table-2 integer counts; no asymptotic notation or rounding is used.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.2 and Equation (21), printed pp. 53-54; exact Table 2 specialization on printed pp. 58-59; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_component_multinomial_entropy_polynomial_lower
    (m : ℕ) (hm : 0 < m) :
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits MME.DWZSquare.alpha) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 15 *
        (Nat.multinomial Finset.univ
          (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) : ℝ) := by
  sorry
