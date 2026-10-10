-- Prove2me | Theorems.Thm_ZipfLaw_zipfMandelbrotPMF_hasSum_one
-- name    : ZipfLaw.zipfMandelbrotPMF_hasSum_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:33.147511+00:00
-- url     : https://prove2.me/theorems/a37de8e9-9899-4058-9357-6e3c24db13e4
-- title:
--   Zipf–Mandelbrot law with Hurwitz-zeta normalization is a distribution
-- statement:
--   Let $s>1$ and $q\ge0$. With normalizing constant $C=\zeta(s,q+1)=\sum_{k\ge1}(k+q)^{-s}$ (Hurwitz zeta), the Zipf–Mandelbrot frequencies
--   $$f(k;q,s)=\frac{1}{C}\,\frac{1}{(k+q)^s},\qquad k=1,2,3,\dots$$
--   form a probability distribution:
--   $$\sum_{k=1}^{\infty}f(k;q,s)=1 .$$
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Related laws" ($f(k;N,q,s)=\frac1C\frac1{(k+q)^s}$; "The constant C is the Hurwitz zeta function evaluated at s").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfMandelbrotPMF_hasSum_one (q s : ℝ) (hq : 0 ≤ q) (hs : 1 < s) :
    HasSum (fun k : ℕ => zipfMandelbrotPMF q s k) 1 := by sorry

end ZipfLaw
