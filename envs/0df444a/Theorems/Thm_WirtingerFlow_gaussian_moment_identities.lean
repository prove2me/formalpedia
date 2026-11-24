-- Prove2me | Theorems.Thm_WirtingerFlow_gaussian_moment_identities
-- name    : WirtingerFlow.gaussian_moment_identities
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:06:51.177601+00:00
-- url     : https://prove2.me/theorems/f28782f6-f7c1-4d8d-9da9-f1d923a804ca
-- title:
--   Lemma 7.3: moment identities in the Gaussian model
-- statement:
--   Let $a\in\mathbb{C}^n$ have i.i.d. coordinates with law $\mathcal N(0,\frac12)+i\,\mathcal N(0,\frac12)$, and let $u,v\in\mathbb{C}^n$ be fixed with $\|u\|=\|v\|=1$. Then
--
--   $$\mathbb E\big[(\operatorname{Re}(u^*aa^*v))^2\big]=\frac12+\frac32(\operatorname{Re}(u^*v))^2-\frac12(\operatorname{Im}(u^*v))^2,$$
--
--   $$\mathbb E\big[\operatorname{Re}(u^*aa^*v)\,|a^*v|^2\big]=2\operatorname{Re}(u^*v),$$
--
--   and $\mathbb E\big[|a^*v|^{2k}\big]=k!$ for every integer $k\ge0$.
--
--   These moments give the mean and variance estimates behind the local curvature bound in the Gaussian model.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Lemma 7.3, eqs. (7.5)-(7.7), p. 21; proof in Appendix A.3, p. 37

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem gaussian_moment_identities {n : ℕ} (u v : Sig n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∫ a, ((inner ℂ u (toSig a) * inner ℂ (toSig a) v).re) ^ 2 ∂(cnGauss n) =
      1 / 2 + 3 / 2 * (inner ℂ u v).re ^ 2 - 1 / 2 * (inner ℂ u v).im ^ 2 ∧
    ∫ a, (inner ℂ u (toSig a) * inner ℂ (toSig a) v).re * ‖inner ℂ (toSig a) v‖ ^ 2 ∂(cnGauss n) =
      2 * (inner ℂ u v).re ∧
    ∀ k : ℕ, ∫ a, ‖inner ℂ (toSig a) v‖ ^ (2 * k) ∂(cnGauss n) = (k.factorial : ℝ) := by sorry

end WirtingerFlow
