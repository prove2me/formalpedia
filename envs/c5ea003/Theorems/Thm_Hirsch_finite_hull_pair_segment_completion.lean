-- Prove2me | Theorems.Thm_Hirsch_finite_hull_pair_segment_completion
-- name    : Hirsch.finite_hull_pair_segment_completion
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T05:03:15.315126+00:00
-- url     : https://prove2.me/theorems/f8820d5a-523e-42b2-a856-1ebfaf2c93db
-- title:
--   Construct an explicit quadratic-generator zonotopal completion of every finite convex hull
-- statement:
--   For arbitrary natural d, positive n and arbitrary real vectors v_0,...,v_(n-1) in R^d, define Z as the actual sum over all n^2 ordered pairs of closed segments [v_i,v_j], with explicit coefficients in [0,1]. Define Q={q: q+v_i belongs to Z for every original generator i}. Prove Z and Q are compact and convex, Q is nonempty, and Z=conv(v_i)+Q as whole sets. In particular the specified finite convex hull is an actual Minkowski summand of this explicit segment-sum completion. No summand, support equality, rank, independence, full dimension, distinct generators, or generic objective is assumed. The construction includes repeated/interior generators, lower dimensions, d=0 and n=1. The n^2 count is the number of presented segment positions, including diagonal and repeated positions, not the number of irredundant facets or a minimal generator count. No original-edge route or polynomial-in-H-row bound is concluded.
-- source:
--   Concrete completion obligation after accepted #309 summand route contraction and #310 arbitrary original-H endpoint lifting. Neither accepted theorem is resubmitted or imported as an assumption: this independent complete construction supplies a genuine finite-generator summand equality. The direct support witness chooses a maximizing original generator k and chooses v_k on all ordered segment slots (k,i), then a single endpoint replacement proves all generator translations lie in Z. Standard pinned Mathlib compactness and Hahn-Banach separation finish whole-set equality. The classical normal-fan/Minkowski-summand viewpoint is credited, e.g. Deformed Graphical Zonotopes, Discrete & Computational Geometry (2023), DOI10.1007/s00454-023-00586-x; no historical-priority or best-completion claim is made. Generator count and original-facet count are explicitly separated.

import Mathlib
open scoped BigOperators Pointwise
set_option autoImplicit false

theorem Hirsch.finite_hull_pair_segment_completion (d n : ℕ) (hn : 0 < n) (v : Fin n → (Fin d → ℝ)) :
    let Z : Set (Fin d → ℝ) :=
      {z | ∃ t : (Fin n × Fin n) → ℝ,
        (∀ e, 0 ≤ t e ∧ t e ≤ 1) ∧
        (∑ e : Fin n × Fin n, (t e • v e.1+(1-t e) • v e.2))=z}
    let Q : Set (Fin d → ℝ) := {q | ∀ i, q+v i ∈ Z}
    IsCompact Z ∧ Convex ℝ Z ∧ IsCompact Q ∧ Convex ℝ Q ∧ Q.Nonempty ∧
      Z = {z | ∃ p ∈ convexHull ℝ (Set.range v), ∃ q ∈ Q, p+q=z} ∧
      Fintype.card (Fin n × Fin n) = n^2 := by sorry
