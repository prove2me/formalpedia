-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
-- name    : mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:20:34.467729+00:00
-- url     : https://prove2.me/theorems/8eb5d84b-3f9d-4c1f-a3c4-a5b756dee89f
-- title:
--   Asymptotic rank of a positive Kronecker power
-- statement:
--   Let $X$ be an order-$d$ tensor with $d\ge 2$, and let $N\ge 1$. Then asymptotic rank is exactly multiplicative under the $N$-fold Kronecker power: $$\widetilde R(X^{\otimes N})=\widetilde R(X)^N.$$ This is the positive-exponent power law obtained from Fekete convergence for the submultiplicative rank sequence; it supplies the substantive case of the Kronecker-power bound used in the Coppersmith–Winograd asymptotic-rank argument.
-- source:
--   Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2212.11824, Definitions 2.5 and 2.8 and the Fekete power law.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality
open MME
universe u

theorem mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X : TensorObj K d) (N : ℕ) (hN : 1 ≤ N) :
    tensorAsymptoticRank (X.kronPow N) = tensorAsymptoticRank X ^ N := by sorry
