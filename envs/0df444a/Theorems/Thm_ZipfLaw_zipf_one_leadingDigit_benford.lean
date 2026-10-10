-- Prove2me | Theorems.Thm_ZipfLaw_zipf_one_leadingDigit_benford
-- name    : ZipfLaw.zipf_one_leadingDigit_benford
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:50.356089+00:00
-- url     : https://prove2.me/theorems/93d4cca7-9afc-4fe0-9461-cd45c00698df
-- title:
--   Leading digits of Zipf ($s=1$) data follow Benford's law
-- statement:
--   Let $K_N$ be a random rank drawn from the Zipf distribution with $s=1$ on $\{1,\dots,N\}$, $\mathbb P(K_N=k)=\frac{1}{H_N\,k}$. For every digit $d\in\{1,\dots,9\}$, the probability that the leading decimal digit of $K_N$ equals $d$ tends to the Benford probability:
--   $$\lim_{N\to\infty}\sum_{\substack{1\le k\le N\\ D_{10}(k)=d}}\frac{1}{H_N\,k}=\log_{10}\!\left(1+\frac1d\right).$$
--
--   **Formalization Note.** The source's sentence does not say which numbers' leading digits are meant; this item reads it as the leading digits of the ranks $k$ when $k$ occurs with Zipf ($s=1$) frequency $\propto 1/k$. (The other reading, the leading digits of the values $C/k$ for $k = 1, \dots, N$ counted once each, is the reciprocal sequence, which does not satisfy Benford's law.)
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Related laws" ("The leading digits of data satisfying Zipf's law with s = 1, satisfy Benford's law").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_one_leadingDigit_benford (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k)
      Filter.atTop (nhds (Real.logb 10 (1 + 1 / (d : ℝ)))) := by sorry

end ZipfLaw
