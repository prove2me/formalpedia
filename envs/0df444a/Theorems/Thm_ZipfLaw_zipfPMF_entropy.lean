-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_entropy
-- name    : ZipfLaw.zipfPMF_entropy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:54.829425+00:00
-- url     : https://prove2.me/theorems/67f9705e-99e7-4852-8806-bfb0baaefc89
-- title:
--   Entropy of the Zipf distribution
-- statement:
--   For $N\ge1$ and real $s$, the Shannon entropy (in nats) of the Zipf distribution is
--   $$-\sum_{k=1}^N f(k;N,s)\ln f(k;N,s)=\frac{s}{H_{N,s}}\sum_{k=1}^N\frac{\ln k}{k^s}+\ln H_{N,s}.$$
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, infobox (Entropy $\frac{s}{H_{N,s}}\sum_{k=1}^N\frac{\ln k}{k^s}+\ln H_{N,s}$).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_entropy (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    -(∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
      s / genHarmonic N s * (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) +
        Real.log (genHarmonic N s) := by sorry

end ZipfLaw
