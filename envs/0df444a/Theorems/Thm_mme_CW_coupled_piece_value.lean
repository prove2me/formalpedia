-- Prove2me | Theorems.Thm_mme_CW_coupled_piece_value
-- name    : mme_CW_coupled_piece_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-23T23:39:27.755066+00:00
-- url     : https://prove2.me/theorems/cc3e4191-a5ac-4d32-9f6f-cd347ca64e2e
-- title:
--   Value lower bound for the coupled CW constituent
-- statement:
--   Let $q\ge3$ and $\tau$ satisfy $3\tau\ge2$. For the explicit four-sum coupled constituent $D_q$ from the tensor square, its cyclically symmetrized value obeys $$V_\tau(D_q)\ge 2^{2/3}q^\tau(q^{3\tau}+2)^{1/3}.$$ The value predicate is witnessed by restrictions of arbitrarily large tensor powers to unrestricted finite direct sums of concrete matrix-multiplication tensors. This is the lemma proved by the Salem--Spencer pruning argument on journal pp. 270--272.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), lemma and proof on journal pp. 270--272 (PDF pp. 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_coupled_piece_value
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    HasSymmetricTauValueAtLeast (coupledObj K q) tau
      ((2 : ℝ) ^ ((2 : ℝ) / 3) *
       (q : ℝ) ^ tau *
       (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) := by sorry
