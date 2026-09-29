-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
-- name    : mme_CW_q6_coupled_raw_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:13:28.833431+00:00
-- url     : https://prove2.me/theorems/04e20a71-20d1-40b7-ad76-aa6de2a5aaf7
-- title:
--   Every base below the raw cyclic value is attained for the coupled $q=6$ constituent
-- statement:
--   Let $D_6$ be the coupled Coppersmith--Winograd constituent, fix $\tau$ with $3\tau\ge2$, and define its limiting raw cyclic base by
--
--   $$
--   R(\tau)=4\,6^{3\tau}(6^{3\tau}+2).
--   $$
--
--   For every real number $V$ with $0\le V<R(\tau)$, the cyclic symmetrization $D_6\otimes\pi(D_6)\otimes\pi^2(D_6)$ has tau-value at least $V$.
--
--   This is the rate-correct asymptotic form of the coupled-constituent lemma: every strict sub-bound is witnessed by concrete finite direct-sum restrictions along arbitrarily large even tensor powers. The open endpoint is intentional and absorbs the Stirling and Salem--Spencer subexponential losses in the paper's nth-root estimate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-constituent lemma and proof on journal pp. 270--272 (PDF pp. 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_q6_coupled_raw_cyclic_value_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V := by sorry
