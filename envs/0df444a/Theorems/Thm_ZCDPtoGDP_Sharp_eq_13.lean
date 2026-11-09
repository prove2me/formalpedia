-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_eq_13
-- name    : ZCDPtoGDP.Sharp.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:41.528091+00:00
-- url     : https://prove2.me/theorems/337c5587-50ca-42b6-bedd-07247e44706c
-- title:
--   §B.2, eq. (13) — the selected Rényi order: $K_{\mathrm{zCDP}}(p,q)\ge D_{\eta^*}/\eta^*=K(c,d)$
-- statement:
--   Let $c>0$ and $d>0$, and put $p=\sigma(c-d)$, $q=\sigma(c+d)$ (so the log-odds of $p$ and $q$ are $u=c-d$ and $v=c+d$) and $\eta^*=1+c/d$. Then $\eta^*>1$ and
--   $$K_{\mathrm{zCDP}}(p,q)\ \ge\ \frac{D_{\eta^*}(\mathrm{Bern}(p)\|\mathrm{Bern}(q))}{\eta^*}\ =\ K(c,d)=\frac dc\,[h(c+d)-h(c-d)],$$
--   where $h(s)=\log\cosh(s/2)$.
--
--   Evaluating the Rényi divergence at this one order, instead of taking the supremum over all orders, gives a closed-form lower bound on the zCDP budget of the Bernoulli pair.
--
--   Differences from the source:
--   - encoding: real-valued D_{η*}/η* and K(c,d) → values in EReal, with K(c,d) embedded; reason: Lean convention, since K_zCDP and D_η are extended reals; same instances
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, §B.2, eq. (13), p. 15

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- §B.2, eq. (13), p. 15: for `c > 0`, `d > 0`, `p = σ(c - d)`, `q = σ(c + d)` and the
selected order `η* = 1 + c/d > 1`,
`K_zCDP(p,q) ≥ D_{η*}(Bern p‖Bern q)/η* = K(c,d) = (d/c)[h(c+d) - h(c-d)]`. -/
theorem eq_13 (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    let p := Real.sigmoid (c - d)
    let q := Real.sigmoid (c + d)
    let ηs := 1 + c / d
    1 < ηs ∧
      ((ηs⁻¹ : ℝ) : EReal) * renyiDiv ηs (bern p) (bern q) ≤ kZCDP p q ∧
      ((ηs⁻¹ : ℝ) : EReal) * renyiDiv ηs (bern p) (bern q) = ((kBound c d : ℝ) : EReal) := by sorry

end ZCDPtoGDP.Sharp
