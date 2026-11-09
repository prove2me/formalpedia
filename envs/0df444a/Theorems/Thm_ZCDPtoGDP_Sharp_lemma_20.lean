-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_lemma_20
-- name    : ZCDPtoGDP.Sharp.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:06.156759+00:00
-- url     : https://prove2.me/theorems/6710a32d-1ab9-44d4-8624-bc3a27683f08
-- title:
--   Lemma 20 — the zCDP Bernoulli comparison $K_{\mathrm{zCDP}}(p,q)\ge\mu^{-1}_{\mathrm{zCDP}}(m_{p,q})$, with equality for symmetric pairs
-- statement:
--   For $0<p<q<1$ let $m_{p,q}=\Phi^{-1}(q)-\Phi^{-1}(p)$ be the Gaussian separation of the Bernoulli pair and
--   $$K_{\mathrm{zCDP}}(p,q)=\sup_{\eta>1}\frac1\eta\max\{D_\eta(\mathrm{Bern}(p)\|\mathrm{Bern}(q)),D_\eta(\mathrm{Bern}(q)\|\mathrm{Bern}(p))\}$$
--   its zCDP budget. Then
--   $$K_{\mathrm{zCDP}}(p,q)\ \ge\ \mu^{-1}_{\mathrm{zCDP}}(m_{p,q}),\qquad \mu^{-1}_{\mathrm{zCDP}}(m)=(2\Phi(m/2)-1)\log\frac{\Phi(m/2)}{\Phi(-m/2)}.\tag{25}$$
--   Equality holds for every symmetric pair $p=\sigma(-a)$, $q=\sigma(a)$ with $a>0$, whose Gaussian separation is $m_{p,q}=2\Phi^{-1}(\sigma(a))$.
--
--   Among all Bernoulli pairs with a given Gaussian separation, randomized response has the smallest zCDP budget. This is the analytic core of the sharp conversion.
--
--   Differences from the source:
--   - reading: equality for the symmetric pair p = σ(−a), q = σ(a) → for every a > 0; reason: a > 0 is exactly the condition 0 < p < q < 1 of the lemma for the symmetric pair
--   - encoding: real-valued μ⁻¹_zCDP(m_{p,q}) compared with K_zCDP → embedded in EReal; reason: K_zCDP is an extended-real supremum; same instances
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Lemma 20, eq. (25), p. 21

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- Lemma 20 (The zCDP Bernoulli comparison), p. 21, eq. (25): for `0 < p < q < 1`,
`K_zCDP(p,q) ≥ μ⁻¹_zCDP(m_{p,q})`; equality holds for every symmetric pair
`p = σ(-a)`, `q = σ(a)` (`a > 0`), whose Gaussian separation is `2Φ⁻¹(σ(a))`. -/
theorem lemma_20 :
    (∀ p q : ℝ, 0 < p → p < q → q < 1 →
      ((muZCDPInv (mSep p q) : ℝ) : EReal) ≤ kZCDP p q) ∧
    ∀ a : ℝ, 0 < a →
      mSep (Real.sigmoid (-a)) (Real.sigmoid a) = 2 * stdNormalQuantile (Real.sigmoid a) ∧
      kZCDP (Real.sigmoid (-a)) (Real.sigmoid a) =
        ((muZCDPInv (mSep (Real.sigmoid (-a)) (Real.sigmoid a)) : ℝ) : EReal) := by sorry

end ZCDPtoGDP.Sharp
