-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_variance
-- name    : ZipfLaw.zipfPMF_variance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:24.07398+00:00
-- url     : https://prove2.me/theorems/fd2d814e-cf40-467b-a87f-4b217ac1803e
-- title:
--   Variance of the Zipf distribution
-- statement:
--   For $N\ge1$ and real $s$, the variance of the rank under the Zipf distribution is
--   $$\sum_{k=1}^N k^2 f(k;N,s)-\Big(\sum_{k=1}^N k\,f(k;N,s)\Big)^2=\frac{H_{N,s-2}}{H_{N,s}}-\frac{H_{N,s-1}^2}{H_{N,s}^2}.$$
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, infobox (Variance $\frac{H_{N,s-2}}{H_{N,s}}-\frac{H^2_{N,s-1}}{H^2_{N,s}}$).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_variance (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := by sorry

end ZipfLaw
