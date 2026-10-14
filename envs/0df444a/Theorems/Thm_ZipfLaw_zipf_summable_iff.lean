-- Prove2me | Theorems.Thm_ZipfLaw_zipf_summable_iff
-- name    : ZipfLaw.zipf_summable_iff
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:01.752508+00:00
-- url     : https://prove2.me/theorems/dd0d92d9-1846-4951-8189-03dca5f30959
-- title:
--   The Zipf p-series converges exactly for $s>1$
-- statement:
--   For a real exponent $s\ge0$, the series $\sum_{k=1}^{\infty} k^{-s}$ is summable if and only if $s>1$. This is the convergence criterion in the infinite-extension theorem, isolated for reuse in both its convergent and divergent branches.
-- source:
--   Wikipedia, "Zipf's law", https://en.wikipedia.org/wiki/Zipf%27s_law, section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, derived from its displayed PMF and generalized harmonic sum.

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_summable_iff (s : ℝ) (hs : 0 ≤ s) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s := by sorry

end ZipfLaw
