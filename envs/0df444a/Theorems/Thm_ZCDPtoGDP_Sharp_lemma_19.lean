-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_lemma_19
-- name    : ZCDPtoGDP.Sharp.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:59.082121+00:00
-- url     : https://prove2.me/theorems/36d2f8ef-ccdc-4535-bad4-2cbfee5fee33
-- title:
--   Lemma 19 — symmetrization at fixed Gaussian separation: $K(c,d)\ge K(0,a)=a\tanh(a/2)$
-- statement:
--   Let $g(u)=\Phi^{-1}(\sigma(u))$ and let $K(c,d)=\frac dc[h(c+d)-h(c-d)]$ for $c>0$, $K(0,d)=d\tanh(d/2)$, with $h(s)=\log\cosh(s/2)$. Let $c\ge0$, $d>0$ and $a>0$ satisfy
--   $$g(c+d)-g(c-d)=2g(a).$$
--   Then
--   $$K(c,d)\ \ge\ K(0,a)=a\tanh(a/2).$$
--
--   Among Bernoulli pairs $p=\sigma(c-d)$, $q=\sigma(c+d)$ with a fixed Gaussian separation, the symmetric pair (randomized response) minimizes the selected-order bound $K$.
--
--   Differences from the source: none.
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Lemma 19, p. 20 (proof pp. 20–21)

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- Lemma 19 (Symmetrization at fixed Gaussian separation), p. 20: if `c ≥ 0`, `d > 0`,
`a > 0` and `g(c + d) - g(c - d) = 2 g(a)`, then `K(c,d) ≥ K(0,a) = a tanh(a/2)`. -/
theorem lemma_19 (c d a : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (ha : 0 < a)
    (hsep : gFun (c + d) - gFun (c - d) = 2 * gFun a) :
    kBound 0 a ≤ kBound c d ∧ kBound 0 a = a * Real.tanh (a / 2) := by sorry

end ZCDPtoGDP.Sharp
