-- Prove2me | Theorems.Thm_ZipfLaw_zipf_infinite_extension
-- name    : ZipfLaw.zipf_infinite_extension
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:43.121933+00:00
-- url     : https://prove2.me/theorems/3db55d74-324f-4340-aed9-9dbf6411b23f
-- title:
--   Zipf extends to infinitely many items iff $s>1$; then $H_{N,s}\to\zeta(s)$
-- statement:
--   Let $s\ge0$. Then:
--
--   1. $\displaystyle\sum_{k=1}^\infty\frac{1}{k^s}$ converges if and only if $s>1$;
--   2. if $s>1$, then $H_{N,s}\to\zeta(s)$ as $N\to\infty$, where $\zeta$ is Riemann's zeta function;
--   3. if $s\le1$, then $H_{N,s}\to+\infty$ as $N\to\infty$.
--
--   So the generalized Zipf distribution can be extended to infinitely many items exactly when $s>1$, and then its normalizing constant is $\zeta(s)$ (the zeta distribution, or Lotka's law). This is the goal theorem of the mission.
--
--   **Formalization Note.** Item 2 is stated in $\mathbb C$ against Mathlib's `riemannZeta`, which is defined on all of $\mathbb C$ by analytic continuation. Summability is that of $k\mapsto 1/(k+1)^s$ over $k \in \mathbb N$.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Formal definition" ("The generalized Zipf distribution can be extended to infinitely many items (N = ∞) only if the exponent s exceeds 1. In that case, the normalization constant H_{N,s} becomes Riemann's zeta function ... If the exponent s is 1 or less, the normalization constant H_{N,s} diverges as N tends to infinity").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_infinite_extension (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by sorry

end ZipfLaw
