-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_signed_estimator_error
-- name    : ZLIPPadding.Padding.Supplement.signed_estimator_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:22:04.927867+00:00
-- url     : https://prove2.me/theorems/3c1b742c-8941-4049-b55a-848fd1d3d053
-- title:
--   Lemma 4.5 — Error of the signed moment estimator
-- statement:
--   In the nonempty uniform-shell setting with $n\ge2$ and $m\ge1$, suppose $|\kappa|\ge\kappa_0>0$, $\tau\ge0$, $|\widehat\mu_4-\mu_4|\le\tau$ and $\tau\le c_n\kappa_0^2/2$. Use the source estimator $\widehat\kappa=\operatorname{sgn}(\kappa)\sqrt{\max\{0,(\widehat\mu_4-b_{n,m})/c_n\}}$ and $\widehat\beta=(m^2/n-\widehat\kappa)/(n+2)$. Then
--
--   $$\frac{\widehat\mu_4-b_{n,m}}{c_n}>0,\qquad |\widehat\kappa-\kappa|\le\frac{\tau}{c_n\kappa_0},\qquad |\widehat\beta-\beta|\le\frac{\tau}{n(n-1)\kappa_0}.$$
--
--   The lemma permits arbitrary scalar estimates satisfying the displayed error hypothesis, including the empirical pair statistic. It preserves both signs and includes zero tolerance.
--
--   Differences from the source:
--   - generalization: the empirical pairwise scalar estimate defined in (4.13) → an arbitrary real scalar estimate satisfying the same error bound; reason: the algebraic estimate holds for every such scalar; substituting the empirical statistic recovers every instance and conclusion of the source lemma
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 19 (PDF p. 20), Lemma 4.5

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem signed_estimator_error (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m)
    (hne : (shell n m).Nonempty) (kap0 tau muHat : ℝ)
    (hk0 : 0 < kap0) (hkap : kap0 ≤ |shellKappa n m|) (htau : 0 ≤ tau)
    (herr : |muHat-(bNM n m+cN n*shellKappa n m^2)| ≤ tau)
    (hsmall : tau ≤ cN n*kap0^2/2) :
    let sign : ℝ := if 0 < shellKappa n m then 1 else if shellKappa n m = 0 then 0 else -1
    let kh := estimateKappa n m sign muHat
    0 < (muHat-bNM n m)/cN n ∧
    |kh-shellKappa n m| ≤ tau/(cN n*kap0) ∧
    |estimateBeta n m kh-shellBeta n m| ≤ tau/((n : ℝ)*(n-1)*kap0) := by sorry

end ZLIPPadding.Padding.Supplement
