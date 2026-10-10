-- Prove2me | Theorems.Thm_ZipfLaw_zipfPMF_ratio
-- name    : ZipfLaw.zipfPMF_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:19.309428+00:00
-- url     : https://prove2.me/theorems/1f2b24c3-2e4c-4979-b6dc-273061017e66
-- title:
--   $f(1)/f(n)=n^s$: the top item is $n^s$ times as frequent as the $n$-th
-- statement:
--   For $1\le n\le N$ and real $s$, the most probable item is exactly $n^s$ times as probable as the item of rank $n$:
--   $$\frac{f(1;N,s)}{f(n;N,s)}=n^{s}.$$
--   For $s=1$: the most common word occurs $n$ times as often as the $n$-th most common one.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, lead section and "Word frequencies in human languages" ("the most common word occurs about n times the n-th most common one").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_ratio (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := by sorry

end ZipfLaw
