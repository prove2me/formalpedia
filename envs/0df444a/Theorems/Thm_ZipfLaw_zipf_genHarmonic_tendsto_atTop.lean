-- Prove2me | Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_atTop
-- name    : ZipfLaw.zipf_genHarmonic_tendsto_atTop
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:27:46.267329+00:00
-- url     : https://prove2.me/theorems/f0a0ba06-47c3-4c10-b63c-f396c8d1c474
-- title:
--   For $0\le s\le1$, the Zipf harmonic sums tend to infinity
-- statement:
--   For every real exponent $0\le s\le1$, the generalized harmonic sums $H_{N,s}$ tend to $+\infty$ as $N\to\infty$. In particular no finite normalizing constant can extend these finite Zipf laws to infinitely many ranks.
-- source:
--   Wikipedia, "Zipf's law", https://en.wikipedia.org/wiki/Zipf%27s_law, section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, derived from its displayed PMF and generalized harmonic sum.

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_genHarmonic_tendsto_atTop (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop := by sorry

end ZipfLaw
