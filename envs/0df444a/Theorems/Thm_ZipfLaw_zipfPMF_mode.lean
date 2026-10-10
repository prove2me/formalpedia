-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_mode
-- name    : ZipfLaw.zipfPMF_mode
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:47.418658+00:00
-- url     : https://prove2.me/theorems/174e811f-b86f-4ba0-9c38-10b06f8880d2
-- title:
--   Rank $1$ is a mode of the Zipf distribution ($s\ge0$)
-- statement:
--   For $N\ge1$ and exponent $s\ge0$, the element of rank $1$ is a most probable element of the Zipf distribution: for every natural number $k$,
--   $$f(k;N,s)\le f(1;N,s)=\frac1{H_{N,s}}.$$
--   (For $s=0$ the distribution is uniform and every rank is a mode.)
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, infobox (Mode $1$; parameters $s\ge0$).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_mode (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := by sorry

end ZipfLaw
