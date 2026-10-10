-- Prove2me | Theorems.Thm_ZipfLaw_log_zipfPMF_affine
-- name    : ZipfLaw.log_zipfPMF_affine
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:51.71368+00:00
-- url     : https://prove2.me/theorems/51ed4521-43d5-49f9-9eff-95300c416e5c
-- title:
--   Log–log plot of the Zipf distribution is affine with slope $-s$
-- statement:
--   For $1\le k\le N$ and real $s$,
--   $$\ln f(k;N,s)=-s\ln k-\ln H_{N,s},$$
--   so on a log–log plot (log rank against log frequency) the Zipf distribution lies on a straight line of slope $-s$.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Empirical testing" ("The data conform to Zipf's law with exponent s to the extent that the plot approximates a linear (more precisely, affine) function with slope −s").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem log_zipfPMF_affine (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by sorry

end ZipfLaw
