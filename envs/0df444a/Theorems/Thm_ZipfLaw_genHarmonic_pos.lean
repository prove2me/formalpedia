-- Prove2me | Theorems.Thm_ZipfLaw_genHarmonic_pos
-- name    : ZipfLaw.genHarmonic_pos
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:27:54.477356+00:00
-- url     : https://prove2.me/theorems/c8f6df3c-57b1-4269-8978-bc95c250e35d
-- title:
--   A nonempty generalized harmonic sum is positive
-- statement:
--   For every integer $N\ge1$ and real exponent $s$, the generalized harmonic sum $H_{N,s}=\sum_{k=1}^{N} k^{-s}$ is strictly positive. This ensures that the common normalizing factor can be cancelled and logarithms of supported Zipf probabilities are well-defined.
-- source:
--   Wikipedia, "Zipf's law", https://en.wikipedia.org/wiki/Zipf%27s_law, section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, derived from its displayed PMF and generalized harmonic sum.

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem genHarmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by sorry

end ZipfLaw
