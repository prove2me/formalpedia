-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_lemma_18
-- name    : ZCDPtoGDP.Sharp.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:57.286978+00:00
-- url     : https://prove2.me/theorems/bfc57534-d014-4998-b66a-73a162112804
-- title:
--   Lemma 18 — hyperbolic integral comparison $4[h(y)-h(x)]\le(y^2-x^2)w(x)w(y)$
-- statement:
--   Let $h(s)=\log\cosh(s/2)$ and $w(u)=\sqrt{\tanh(u/2)/u}$ for $u\ne0$, $w(0)=1/\sqrt2$. For all real $x,y$ with $y>|x|$,
--   $$4\,[h(y)-h(x)]\le(y^2-x^2)\,w(x)\,w(y).\tag{20}$$
--
--   This is the second inequality behind the symmetrization argument (Lemma 19). It compares an average of $w^2$ over $[x^2,y^2]$, after the change of variables $t=u^2$, with the geometric mean of its endpoint values.
--
--   Differences from the source: none.
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Lemma 18, eq. (20), p. 19

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- Lemma 18 (Hyperbolic integral comparison), p. 19, eq. (20): for `y > |x|`,
`4[h(y) - h(x)] ≤ (y² - x²) w(x) w(y)`. -/
theorem lemma_18 (x y : ℝ) (hxy : |x| < y) :
    4 * (hFun y - hFun x) ≤ (y ^ 2 - x ^ 2) * wFun x * wFun y := by sorry

end ZCDPtoGDP.Sharp
