-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_finite_truncation
-- name    : ZigZagStrong.ZigZag.finite_truncation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:33.050203+00:00
-- url     : https://prove2.me/theorems/0c3ec498-6b45-44f2-b103-4532079f1733
-- title:
--   Lemma A.4 — the specified truncation preserves the top spectral edge
-- statement:
--   Let $H$ satisfy the sharp-edge assumptions and let $X$ be the infinite root component obtained by the specified finite edge deletion from $X_H$. With $\lambda_+(A)=\sup\operatorname{spec}(A)$,
--   $$\lambda_+(A_X)=\lambda_+(A_{X_H}).$$
--   The operator on $X$ is constructed by deleting those actual adjacency entries and compressing to the closed square-summable root-component subspace. This removes the truncation from the edge computation.
--
--   Differences from the source:
--   - encoding: Adjacency on the root component of the infinite graph → Compression of the finite-rank edge-deletion operator to the closed span of its reachable coordinate vectors; reason: This is its actual complex l2 adjacency; the top edge uses real parts of a self-adjoint spectrum.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Lemma A.4, p. 28.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem finite_truncation {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
  topEdge (truncatedAdj H a t) = topEdge (matchingLimit H) := by sorry

end ZigZagStrong.ZigZag
