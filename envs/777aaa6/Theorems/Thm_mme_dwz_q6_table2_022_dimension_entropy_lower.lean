-- Prove2me | Theorems.Thm_mme_dwz_q6_table2_022_dimension_entropy_lower
-- name    : mme_dwz_q6_table2_022_dimension_entropy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:40:06.518883+00:00
-- url     : https://prove2.me/theorems/da0979c9-9263-465d-9c23-16afafd7bd9c
-- title:
--   Polynomial-loss entropy lower bound for the Table-2 022/202 prescribed dimension
-- statement:
--   For an integer $t>0$, set $m=10^8t$, $L=3477403t$, and $G=93045194t$. Let $D_t$ be the exact prescribed-word dimension extracted from the canonical $022$ and $202$ blocks, so that $D_t=\binom{m}{L}\binom{m-L}{L}6^{2G}$. If $p=(L/m,G/m,L/m)$, prove the finite bound
--
--   $$
--   \exp\!\bigl(m\log(2)H_2(p)\bigr)\,6^{2G}
--   \leq (6(m+1))^3 D_t.
--   $$
--
--   This is the explicit method-of-types estimate connecting the exact finite restriction dimension to its entropy rate. The only loss is the displayed degree-three polynomial, which is subexponential along the divisible Table-2 sequence.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173. The finite polynomial-loss estimate is the standard method-of-types/Stirling bridge applied to the exact 022/202 dimension formula.

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction

open scoped BigOperators
open MME MME.DWZSquare MME.DWZTable2Component022

set_option autoImplicit false

theorem mme_dwz_q6_table2_022_dimension_entropy_lower
    (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    let profile : Fin 3 → ℝ := ![splitA, 1 - 2 * splitA, splitA]
    Real.exp
        ((m : ℝ) * Real.log 2 * mme_modern_entropyBits profile) *
        ((6 ^ (2 * G) : ℕ) : ℝ) ≤
      (6 * (((m + 1 : ℕ) : ℝ))) ^ 3 * (D : ℝ) := by
  sorry
