-- Prove2me | Theorems.Thm_mme_CW_square_asymptoticRank_le
-- name    : mme_CW_square_asymptoticRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:30:58.319093+00:00
-- url     : https://prove2.me/theorems/c1b67fd7-1a6d-49d5-9a0b-734e66acf855
-- title:
--   Asymptotic-rank budget for the square of the CW tensor
-- statement:
--   The characteristic-free border-rank certificate for the Coppersmith--Winograd tensor has budget $q+2$. Taking its Kronecker square and using multiplicativity of degeneration/rank witnesses gives
--
--   $$
--   \widetilde R(T_q\otimes T_q)\le(q+2)^2.
--   $$
--
--   This is the rank budget paired with the tensor-square laser-value witness in the Section-8 auxiliary inequality.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (10) and the squared rank budget used in the auxiliary equation on journal pp. 263 and 269 (PDF pp. 13 and 19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_CW_square_asymptoticRank_le
    {K : Type u} [Field K] (q : ℕ) :
    tensorAsymptoticRank (TensorObj.kron (CWObj K q) (CWObj K q)) ≤
      ((q : ℝ) + 2) ^ (2 : ℕ) := by sorry
