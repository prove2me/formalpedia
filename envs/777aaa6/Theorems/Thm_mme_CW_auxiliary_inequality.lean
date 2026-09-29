-- Prove2me | Theorems.Thm_mme_CW_auxiliary_inequality
-- name    : mme_CW_auxiliary_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:25:47.940348+00:00
-- url     : https://prove2.me/theorems/2b5a28e8-ab68-45d9-b84a-082099c7f0c7
-- title:
--   Coppersmith--Winograd coupled laser auxiliary inequality
-- statement:
--   Let $q\ge3$ and put $\tau=\omega_K/3$, with $\omega_K\ge2$. For positive real frequencies $a,b,c,d$ satisfying $$3a+6b+3c+3d=1,$$ the coupled tensor-square extraction gives $$\operatorname{auxiliaryRHS}(q,\tau,a,b,c,d)\le(q+2)^2.$$ The right-hand side is the square of the border-rank base of $T_q$. The left-hand side is exactly the normalized expression on journal p. 269 after substituting the five marginals from equation (13). This theorem is the hard Section 8 laser step: its proof must exhibit the Salem--Spencer-pruned direct sums and use the coupled constituent value, rather than count incompatible blocks.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (11)--(13), coupled extraction on journal pp. 265--269 (PDF pp. 15--19), and the coupled-piece lemma on journal pp. 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_omega_strassen
open MME
universe u

theorem mme_CW_auxiliary_inequality
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q)
    (homega : 2 ≤ matMulExp_strassen K)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1) :
    auxiliaryRHS q (matMulExp_strassen K / 3) a b c d ≤
      ((q : ℝ) + 2) ^ (2 : ℕ) := by sorry
