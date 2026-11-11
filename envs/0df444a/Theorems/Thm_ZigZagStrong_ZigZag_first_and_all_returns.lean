-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_first_and_all_returns
-- name    : ZigZagStrong.ZigZag.first_and_all_returns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:49.131102+00:00
-- url     : https://prove2.me/theorems/be6aa370-28cc-4e5e-824c-4d5ba7ad3e97
-- title:
--   Lemma A.3 — equal radii and closed-walk growth
-- statement:
--   For the same rooted truncation $(X,o)$, let $S_X$ and $C_X$ be the first-return and all-return generating functions. Let $c_\ell$ count all closed walks of length $\ell$ from $o$, including the empty walk at length zero. Then
--   $$R_{S_X}=R_{C_X},\qquad\limsup_{\ell\to\infty}c_\ell^{1/\ell}=\Lambda_H.$$
--   Both conclusions use the same concrete root component as Lemma A.2. This connects the first-return calculation with the adjacency spectral radius.
--
--   Differences from the source:
--   - encoding: Generating-function radii and real coefficient-root limsup → Radii as suprema of convergence radii in ENNReal, and ENNReal limsup; reason: For nonnegative counts real absolute convergence gives the complex power-series radius; infinite values remain representable.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Lemma A.3, p. 28.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem first_and_all_returns {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
  seriesRadius (firstReturnCount H a t) = seriesRadius (closedCount H a t) ∧
  walkGrowth (closedCount H a t) = ENNReal.ofReal (sharpEdge H) := by sorry

end ZigZagStrong.ZigZag
