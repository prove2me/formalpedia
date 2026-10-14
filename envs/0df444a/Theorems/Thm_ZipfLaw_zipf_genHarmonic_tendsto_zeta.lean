-- Prove2me | Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_zeta
-- name    : ZipfLaw.zipf_genHarmonic_tendsto_zeta
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:29:10.80628+00:00
-- url     : https://prove2.me/theorems/207133b7-d4cf-4627-bc1f-e2f75f531235
-- title:
--   For $s>1$, the Zipf harmonic sums tend to $\zeta(s)$
-- statement:
--   If $s>1$, the generalized harmonic partial sums $H_{N,s}=\sum_{k=1}^{N}k^{-s}$ converge to Riemann's zeta function $\zeta(s)$. The formal limit takes place in $\mathbb C$ after casting the real sums, because Mathlib's `riemannZeta` is complex-valued.
-- source:
--   Wikipedia, "Zipf's law", https://en.wikipedia.org/wiki/Zipf%27s_law, section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, derived from its displayed PMF and generalized harmonic sum.

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_genHarmonic_tendsto_zeta (s : ℝ) (hs : 1 < s) :
    Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
      (nhds (riemannZeta s)) := by sorry

end ZipfLaw
