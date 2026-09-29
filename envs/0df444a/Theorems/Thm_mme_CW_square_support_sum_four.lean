-- Prove2me | Theorems.Thm_mme_CW_square_support_sum_four
-- name    : mme_CW_square_support_sum_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:59:23.299545+00:00
-- url     : https://prove2.me/theorems/5ed6f6f1-5863-42c0-b469-08857459e37b
-- title:
--   CW tensor-square support has total grade four
-- statement:
--   Every support type $(i,j,k)$ of the Coppersmith--Winograd tensor satisfies $i+j+k=2$. Therefore, if $s_1=(i_1,j_1,k_1)$ and $s_2=(i_2,j_2,k_2)$ are two supported types, the regrouped tensor-square grades satisfy
--
--   $$
--   (i_1+i_2)+(j_1+j_2)+(k_1+k_2)=4.
--   $$
--
--   This is the support-level invariant $I+J+K=4$ used to split $T_q^{\otimes 2}$ into five coordinate classes in Coppersmith--Winograd equation (11). The natural representatives $0,1,2$ of the finite grades are used in the sum.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (11) and the sentence immediately following it, journal p. 265 (PDF p. 15); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected
open MME

theorem mme_CW_square_support_sum_four
    (s₁ s₂ : Fin 3 × Fin 3 × Fin 3)
    (h₁ : s₁ ∈ CWSupportPattern)
    (h₂ : s₂ ∈ CWSupportPattern) :
    (s₁.1.val + s₂.1.val) +
      (s₁.2.1.val + s₂.2.1.val) +
      (s₁.2.2.val + s₂.2.2.val) = 4 := by sorry
