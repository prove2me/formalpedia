-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_lemma_17
-- name    : ZCDPtoGDP.Sharp.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:56.944188+00:00
-- url     : https://prove2.me/theorems/5cb3d48a-4849-49fc-a787-2f5faae8a78a
-- title:
--   Lemma 17 — Gaussian derivative comparison: $g'/w$ is nonincreasing on $[0,\infty)$
-- statement:
--   Let $g(u)=\Phi^{-1}(\sigma(u))$, where $\Phi$ is the standard normal CDF and $\sigma(u)=(1+e^{-u})^{-1}$, and let $w(u)=\sqrt{\tanh(u/2)/u}$ for $u\ne0$, $w(0)=1/\sqrt2$. Then $g$ is differentiable on $\mathbb R$, the function
--   $$u\mapsto\frac{g'(u)}{w(u)}$$
--   is nonincreasing on $[0,\infty)$, and consequently, for all $x,y$ with $y>|x|$,
--   $$\frac{g'(y)}{g'(x)}\le\frac{w(y)}{w(x)}.$$
--
--   This is the first of the two inequalities that drive the symmetrization argument (Lemma 19): it controls how fast the Gaussian separation grows when a Bernoulli pair is moved into the tail.
--
--   Differences from the source:
--   - encoding: g′, whose existence the source uses implicitly → Lean's deriv g, with differentiability of g on ℝ stated as a conclusion; reason: Lean's deriv is 0 where a function is not differentiable, so the conclusion asserts that the source's derivative exists
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Lemma 17, p. 16 (proof pp. 17–18); g p. 15, w p. 16

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- Lemma 17 (Gaussian derivative comparison), p. 16: `g = Φ⁻¹ ∘ σ` is differentiable,
`u ↦ g'(u)/w(u)` is nonincreasing on `[0, ∞)`, and consequently
`g'(y)/g'(x) ≤ w(y)/w(x)` whenever `y > |x|`. -/
theorem lemma_17 :
    (∀ u : ℝ, DifferentiableAt ℝ gFun u) ∧
    AntitoneOn (fun u => deriv gFun u / wFun u) (Set.Ici 0) ∧
    ∀ x y : ℝ, |x| < y → deriv gFun y / deriv gFun x ≤ wFun y / wFun x := by sorry

end ZCDPtoGDP.Sharp
