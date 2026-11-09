-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_eq_11
-- name    : ZCDPtoGDP.Sharp.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:15.736404+00:00
-- url     : https://prove2.me/theorems/1520ade2-a91c-4f31-9220-14d54e3949ec
-- title:
--   §B.1.3, eqs. (10)–(11) — the inverse conversion $\mu^{-1}_{\mathrm{zCDP}}$, strictly increasing on $[0,\infty)$
-- statement:
--   For a separation $m\ge0$ let
--   $$a=\log\frac{\Phi(m/2)}{\Phi(-m/2)}.$$
--   Then $a\ge0$, $\sigma(a)=\Phi(m/2)$, $2\Phi^{-1}(\sigma(a))=m$, and
--   $$a\tanh(a/2)=\mu^{-1}_{\mathrm{zCDP}}(m)=(2\Phi(m/2)-1)\log\frac{\Phi(m/2)}{\Phi(-m/2)}.$$
--   Moreover $\mu^{-1}_{\mathrm{zCDP}}$ is strictly increasing on $[0,\infty)$.
--
--   Since $a\ge0$ solves $\rho=a\tanh(a/2)$ for $\rho=a\tanh(a/2)$, the first part says $\mu_{\mathrm{zCDP}}(a\tanh(a/2))=2\Phi^{-1}(\sigma(a))=m$: the map $\mu^{-1}_{\mathrm{zCDP}}$ inverts the conversion $\rho\mapsto\mu_{\mathrm{zCDP}}(\rho)$ of Theorem 6.
--
--   Differences from the source:
--   - encoding: μ_zCDP(a tanh(a/2)) = 2Φ⁻¹(σ(a)) = m → a ≥ 0 and 2Φ⁻¹(σ(a)) = m; reason: μ_zCDP(ρ) is 2Φ⁻¹(σ(t)) for the unique t ≥ 0 with t tanh(t/2) = ρ (the goal's clause (i)), and a ≥ 0 is that t for ρ = a tanh(a/2)
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, §B.1.3, eqs. (10)–(11) and the following sentence, p. 14

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- §B.1.3, eqs. (10)–(11), p. 14: for `m ≥ 0` and `a = log(Φ(m/2)/Φ(-m/2))`,
`a ≥ 0`, `σ(a) = Φ(m/2)`, `2Φ⁻¹(σ(a)) = m` and `a tanh(a/2) = μ⁻¹_zCDP(m)`; and
`μ⁻¹_zCDP` is strictly increasing on `[0, ∞)`. -/
theorem eq_11 :
    (∀ m : ℝ, 0 ≤ m →
      let a := Real.log (stdNormalCDF (m / 2) / stdNormalCDF (-m / 2))
      0 ≤ a ∧ Real.sigmoid a = stdNormalCDF (m / 2) ∧
        2 * stdNormalQuantile (Real.sigmoid a) = m ∧
        a * Real.tanh (a / 2) = muZCDPInv m) ∧
    StrictMonoOn muZCDPInv (Set.Ici 0) := by sorry

end ZCDPtoGDP.Sharp
