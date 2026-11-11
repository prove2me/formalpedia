-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_first_return_growth
-- name    : ZigZagStrong.ZigZag.first_return_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:29.702363+00:00
-- url     : https://prove2.me/theorems/4033b19e-0197-4856-8923-d30e9779af68
-- title:
--   Lemma A.2 — growth of first-return walks in the specified truncation
-- statement:
--   Let $H$ satisfy the sharp-edge standing assumptions, and let $(X,o)$ be the specified rooted truncation, with a chosen initial gadget incidence. Let $s_\ell$ count walks of length $\ell$ from $o$ to $o$ with no intermediate return. Then
--   $$\limsup_{\ell\to\infty}s_\ell^{1/\ell}=\Lambda_H.$$
--   The counts are computed from the actual truncated infinite graph, with parallel walks distinguished. This identifies the exponential scale needed by the all-return statement.
--
--   Differences from the source:
--   - encoding: Real limsup of first-return coefficient roots → Extended-nonnegative-real limsup equal to ofReal Lambda_H; reason: The source finite value is retained and an infinite growth value cannot silently become zero; the n=0 power is irrelevant to atTop.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Lemma A.2, p. 27.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem first_return_growth {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
  walkGrowth (firstReturnCount H a t) = ENNReal.ofReal (sharpEdge H) := by sorry

end ZigZagStrong.ZigZag
