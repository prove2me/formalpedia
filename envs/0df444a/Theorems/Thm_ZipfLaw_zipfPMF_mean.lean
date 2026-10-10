-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_mean
-- name    : ZipfLaw.zipfPMF_mean
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:43.198065+00:00
-- url     : https://prove2.me/theorems/2433609e-8cc9-4d45-aa7c-8a19848af3c3
-- title:
--   Mean of the Zipf distribution: $H_{N,s-1}/H_{N,s}$
-- statement:
--   For $N\ge1$ and real $s$, the mean rank under the Zipf distribution is
--   $$\sum_{k=1}^{N}k\,f(k;N,s)=\frac{H_{N,s-1}}{H_{N,s}} .$$
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, infobox (Mean $H_{N,s-1}/H_{N,s}$).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_mean (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k = genHarmonic N (s - 1) / genHarmonic N s := by sorry

end ZipfLaw
