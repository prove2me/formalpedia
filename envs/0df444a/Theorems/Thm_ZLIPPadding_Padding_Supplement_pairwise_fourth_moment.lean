-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_pairwise_fourth_moment
-- name    : ZLIPPadding.Padding.Supplement.pairwise_fourth_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:21:41.25926+00:00
-- url     : https://prove2.me/theorems/aecff56f-f146-423e-a991-25b17e6ba9a7
-- title:
--   Proposition 4.4 — Pairwise fourth-moment identity
-- statement:
--   Let $n\ge2$ and integer $m\ge1$, with nonempty shell $S_m(L)$ in $L=O\mathbb Z^n$. Let $U,V$ be independent uniform shell vectors and write $\mu_4=\mathbb E\langle U,V\rangle^4$. For the actual signed shell coefficient $\kappa$, set $b_{n,m}=3m^4/(n(n+2))$ and $c_n=n(n-1)/(n+2)$. Then
--
--   $$\mu_4=b_{n,m}+c_n\kappa^2.$$
--
--   The statistic determines the magnitude of the signed coefficient; its sign still comes from exact shell counting.
--
--   Differences from the source:
--   - encoding: independent uniform ambient shell vectors → two nested finite expectations of a uniform standard-shell PMF transported by O; reason: these expectations are the exact product law
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 18 (PDF p. 19), Proposition 4.4

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem pairwise_fourth_moment (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m)
    (O : RMat n) (hO : Orthogonal O) (μ : PMF (ZVec n))
    (hμ : UniformOn μ (shell n m)) :
    pairMoment O m μ = bNM n m + cN n * shellKappa n m ^ 2 := by sorry

end ZLIPPadding.Padding.Supplement
