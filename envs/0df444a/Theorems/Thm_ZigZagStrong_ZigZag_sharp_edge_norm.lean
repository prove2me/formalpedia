-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_sharp_edge_norm
-- name    : ZigZagStrong.ZigZag.sharp_edge_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:47.02131+00:00
-- url     : https://prove2.me/theorems/21ecc45a-d09f-432e-b477-d03b8f98eddd
-- title:
--   Proposition 3.13 — the determinant minimum is the infinite adjacency norm
-- statement:
--   Let $H$ be a good vertex-transitive $c$-regular gadget on $d\ge3$ ports, with $c\ge2$, under the standing hypotheses of Section 3.1. The explicit edge satisfies
--   $$\Lambda_H=\|A_{T_d z H}\|.$$
--   The infimum encoding of Eq. (7) attains a minimum at some $x>c^2$. The identity is stated for the matching-tree realization and for every permutation-tree realization when $d=2r$. This keeps the determinant computation separate from the genuine infinite adjacency norm.
--
--   Differences from the source:
--   - encoding: The explicit minimum in Eq. (7) and the unlabeled infinite product → Infimum together with its attainment, and equality for both regular tree realizations; reason: Attainment recovers the source minimum; label independence identifies both models without assuming the norm formula.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Proposition 3.13, p. 15.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem sharp_edge_norm {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) :
  sharpEdge H = ‖matchingLimit H‖ ∧
    (∃ x : ℝ, (c : ℝ)^2 < x ∧ edgeFunction H x = sharpEdge H ∧
      ∀ y : ℝ, (c : ℝ)^2 < y → edgeFunction H x ≤ edgeFunction H y) ∧
    (∀ r : ℕ, ∀ h : d = 2*r,
      sharpEdge H = ‖permutationLimit (h ▸ H)‖) := by sorry

end ZigZagStrong.ZigZag
