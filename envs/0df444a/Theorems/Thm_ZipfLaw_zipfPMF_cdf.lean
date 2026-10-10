-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_cdf
-- name    : ZipfLaw.zipfPMF_cdf
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:05.342107+00:00
-- url     : https://prove2.me/theorems/c21b4a38-f01a-48db-987a-684583516f57
-- title:
--   CDF of the Zipf distribution: $H_{n,s}/H_{N,s}$
-- statement:
--   For integers $N\ge1$, $0\le n\le N$ and real $s$, the cumulative distribution function of the Zipf distribution is
--   $$\sum_{k=1}^{n}f(k;N,s)=\frac{H_{n,s}}{H_{N,s}} .$$
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, infobox (CDF $H_{k,s}/H_{N,s}$).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_cdf (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, zipfPMF N s k = genHarmonic n s / genHarmonic N s := by sorry

end ZipfLaw
