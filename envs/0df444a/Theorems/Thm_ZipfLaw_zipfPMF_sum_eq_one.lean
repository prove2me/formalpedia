-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_sum_eq_one
-- name    : ZipfLaw.zipfPMF_sum_eq_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:28.345312+00:00
-- url     : https://prove2.me/theorems/9f1f191e-020e-45cb-9765-0221bed168dd
-- title:
--   The Zipf distribution sums to $1$
-- statement:
--   For every integer $N\ge1$ and real exponent $s$,
--   $$\sum_{k=1}^{N}f(k;N,s)=\sum_{k=1}^N\frac{1}{H_{N,s}\,k^s}=1 .$$
--
--   This is the statement that $H_{N,s}$ is the normalization constant of the Zipf distribution.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Formal definition" (PMF $f(k;N,s)=\frac{1}{H_{N,s}}\frac{1}{k^s}$, $H_{N,s}$ the normalization constant).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_sum_eq_one (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by sorry

end ZipfLaw
