-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_moment
-- name    : ZipfLaw.zipfPMF_moment
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:17.97358+00:00
-- url     : https://prove2.me/theorems/7a1111e5-8f7a-4838-9116-4d150410c7a8
-- title:
--   All finite Zipf moments are ratios of shifted harmonic sums
-- statement:
--   For every cutoff $N\in\mathbb N$, real exponent $s$, and integer moment order $p\ge0$, the finite Zipf law satisfies $\sum_{k=1}^{N} k^p f(k;s,N)=H_{N,s-p}/H_{N,s}$. The identity includes $N=0$ under Lean's convention for division by zero. The first and second moment formulas in the mission are its special cases.
-- source:
--   Wikipedia, "Zipf's law", https://en.wikipedia.org/wiki/Zipf%27s_law, section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, derived from its displayed PMF and generalized harmonic sum.

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_moment (N : ℕ) (s : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ p * zipfPMF N s k) =
      genHarmonic N (s - p) / genHarmonic N s := by sorry

end ZipfLaw
