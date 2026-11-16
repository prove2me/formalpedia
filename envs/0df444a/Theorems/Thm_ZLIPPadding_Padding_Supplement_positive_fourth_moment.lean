-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_positive_fourth_moment
-- name    : ZLIPPadding.Padding.Supplement.positive_fourth_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:26:09.736759+00:00
-- url     : https://prove2.me/theorems/7ef416d2-0a4b-4b91-8591-fd3ffa3be10c
-- title:
--   Lemma 6.2 — Positive contrast and the full invariant-law classifier
-- statement:
--   Assume $n\ge256$ and integer $1\le m\le n^{3/4}$. Let $\mu$ be any automorphism-invariant law on $S_m(L)$, and put $Z=O^\top X$ for $X\sim\mu$. Define $\alpha_\mu=\mathbb EZ_1^4$, $\beta_\mu=\mathbb EZ_1^2Z_2^2$ and $\kappa_\mu=\alpha_\mu-3\beta_\mu$. Then
--
--   $$\kappa_\mu\ge\frac{m(n+2-3m)}{n(n-1)}\ge\frac m{4n}>0.$$
--
--   The complete label-recovery algorithm applies to independent samples from $\mu$, with the same explicit $N_4,N_x$ bounds of Theorem 4.1 and $\kappa_0=m/(4n)$. It uses the positive sign and the empirical moments of $\mu$; it does not substitute uniform-shell moments or perform unnecessary uniform-shell sign counting. This includes the algorithmic clause of the lemma, not only its inequality.
--
--   Differences from the source:
--   - encoding: moments of the first one and two coordinates of an invariant law → averages over all coordinate choices and uniform finite-program witnesses for its classifier; reason: signed permutation invariance makes these the same moments; the positive sign avoids uniform-shell preprocessing
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 25 (PDF p. 26), Lemma 6.2

import Definitions.Def_ZLIPPadding_Padding_Supplement_Reductions

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem positive_fourth_moment :
    (∀ (n m : ℕ) (μ : PMF (ZVec n)), shortRange n m →
      ShellLaw m μ → SignedInvariant μ →
      momentKappa m μ ≥ (m : ℝ)*(n+2-3*m)/((n : ℝ)*(n-1)) ∧
      (m : ℝ)*(n+2-3*m)/((n : ℝ)*(n-1)) ≥ (m : ℝ)/(4*n) ∧
      0 < (m : ℝ)/(4*n)) ∧
    PositiveLabelRecovery := by sorry

end ZLIPPadding.Padding.Supplement
