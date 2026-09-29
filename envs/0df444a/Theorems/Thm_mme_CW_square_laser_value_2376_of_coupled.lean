-- Prove2me | Theorems.Thm_mme_CW_square_laser_value_2376_of_coupled
-- name    : mme_CW_square_laser_value_2376_of_coupled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T04:54:26.830839+00:00
-- url     : https://prove2.me/theorems/777e1759-c31e-4a08-b3bb-7eabd584bb80
-- title:
--   CW tensor-square tau-value at the exact 2.376 profile
-- statement:
--   Let $q=6$, let $3\tau\ge2$, and use the exact rational frequencies in the Coppersmith--Winograd $2.376$ certificate. If the coupled four-sum constituent has symmetric tau-value
--
--   $$
--   2^{2/3}6^\tau(6^{3\tau}+2)^{1/3},
--   $$
--
--   then the tensor square $T_6\otimes T_6$ has tau-value at least the corresponding exact Section-8 expression $\operatorname{auxiliaryRHS}(6,\tau,a,b,c,d)$. The witness consists of concrete finite direct sums of matrix-multiplication tensors extracted from cofinally many square powers.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square extraction and auxiliary inequality on journal pp. 265--269, using the coupled lemma on pp. 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME
universe u

theorem mme_CW_square_laser_value_2376_of_coupled
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K 6) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (6 : ℝ) ^ tau *
         (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau
      (auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) := by sorry
