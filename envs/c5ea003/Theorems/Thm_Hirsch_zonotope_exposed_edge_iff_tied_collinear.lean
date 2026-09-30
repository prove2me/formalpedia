-- Prove2me | Theorems.Thm_Hirsch_zonotope_exposed_edge_iff_tied_collinear
-- name    : Hirsch.zonotope_exposed_edge_iff_tied_collinear
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T14:41:53.274982+00:00
-- url     : https://prove2.me/theorems/bb32ac53-d8ba-4e21-92eb-b7e5ec568c70
-- title:
--   Exact original exposed-edge test for arbitrary finite segment sums
-- statement:
--   For arbitrary natural d,m, arbitrary real generators w_i in R^d and an arbitrary real linear objective f, let Z be the actual sum of the segments [0,w_i], using all coefficients in [0,1], and let F be the set of points of Z with objective equal to the explicit support sum sum_i max(0,f(w_i)). Prove that F is a nondegenerate closed segment, exposed and extreme in the ORIGINAL Z and with both endpoints actual extreme points of Z, if and only if there is a nonzero objective-tied generator w_j such that every objective-tied generator w_i is a real scalar multiple of w_j. In particular this is a necessary-and-sufficient finite direction criterion, not an assumed projected-cube adjacency. The proof derives the maximum and saturation conditions for every coefficient representation and explicitly constructs the two endpoints when the criterion holds. Repeated, opposite and zero generators, non-full-dimensional bodies, zero objective, m=0 and d=0 are included. No genericity, independence, vertex catalogue, edge oracle or short path is supplied. The theorem does not construct an all-pairs walk, bound diameter, or improve original-H-row complexity.
-- source:
--   Distinct whole-face edge obligation after accepted #311 finite-hull pair-segment completion. Accepted #309 supplies the reused elementary segment-parameter and line-injectivity proof bodies; no accepted public target is resubmitted. All other proof code is direct finite-sum, scalar-interval and exposed-face reasoning on the committed Mathlib pin. This is classical zonotope support-face geometry formalized for arbitrary degenerate presented generators, not historical novelty or a new best diameter bound. The hyperplane-arrangement/zonotope viewpoint is background, e.g. Deza, Hao and Pournin, Sizing the White Whale, arXiv:2205.13309. The root states the complete iff and actual original geometry, not merely a sufficient condition asserted to hold generically.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_exposed_edge_iff_tied_collinear (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    let Z : Set (Fin d → ℝ) := {x | ∃ t : Fin m → ℝ,
      (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ (∑ i : Fin m, t i • w i)=x}
    let F : Set (Fin d → ℝ) := {x | x ∈ Z ∧ f x = ∑ i : Fin m, max 0 (f (w i))}
    (∃ u v : Fin d → ℝ, u ≠ v ∧ F=segment ℝ u v ∧
      IsExposed ℝ Z (segment ℝ u v) ∧ IsExtreme ℝ Z (segment ℝ u v) ∧
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ) ↔
    ∃ j : Fin m, w j ≠ 0 ∧ f (w j)=0 ∧
      ∀ i, f (w i)=0 → ∃ c : ℝ, w i=c • w j := by sorry
