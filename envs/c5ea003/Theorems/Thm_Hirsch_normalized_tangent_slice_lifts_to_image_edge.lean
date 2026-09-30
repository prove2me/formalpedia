-- Prove2me | Theorems.Thm_Hirsch_normalized_tangent_slice_lifts_to_image_edge
-- name    : Hirsch.normalized_tangent_slice_lifts_to_image_edge
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T21:46:21.342716+00:00
-- url     : https://prove2.me/theorems/b531d260-eff2-475a-b25b-e7c941a21ec6
-- title:
--   Normalized tangent-image slices select genuine improving original-image edges
-- statement:
--   For a finite H-system and a linear image, a feasible anchor strict off its selected active rows realizes every selected tangent direction by a positive feasible step. Positive selected-row height weights and a finite row factorization of the image ensure positive height on every nonzero image direction. A uniquely exposed point r of the height-one image tangent slice, together with an attained maximum positive length along r over ALL source lifts, constructs the entire exposed original-image segment from the anchor image to that maximum endpoint. The segment is nondegenerate and extreme, and improves any objective positive on r. The image exposing functional is constructed as f-f(r)h. The normalized slice support and ray optimality are witness interfaces, not source adjacency or an assumed original-image edge. Source compactness, source vertexhood, a one-dimensional preimage face, and image full-dimensionality are not assumptions. The theorem also proves exact equality between the image active-row cone and nonnegative scaled actual image displacements. It makes no polynomial route-length or pivot-bound assertion.
-- source:
--   Classical tangent-cone/vertex-figure and supporting-face geometry, formalized at the missing selection-to-original-image-edge interface. Reuses the finite slack argument and support-extreme argument of accepted #247/#246 with their stated changes. A normalized-slice singleton support is supplied by the accepted fibre-dual theorem applied to the normalized tangent system. Exact LP witness production and lexicographic optimization are implemented separately; not claimed Lean-extracted. Primary background: Ken Clarkson, CIS677 lecture 7, convexity and cone/slice correspondence; Boyd (1995), Resolving degeneracy in combinatorial linear programs: steepest edge, steepest ascent, and parametric ascent, DOI 10.1007/BF01585762.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.normalized_tangent_slice_lifts_to_image_edge
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x y : E) (r : F) (tau : ℝ)
    (h f c : F →ₗ[ℝ] ℝ) (lam : ι → ℝ) (W : ι → F)
    (hx : ∀ i, a i x ≤ b i) (hy : ∀ i, a i y ≤ b i)
    (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i)
    (hlam : ∀ i ∈ J, 0 < lam i)
    (hheight : h.comp G = -(∑ i ∈ J, lam i • a i))
    (himage : ∀ v : E, G v = ∑ i ∈ J, a i v • W i)
    (hr : h r = 1) (htau : 0 < tau) (hcr : 0 < c r)
    (hslice : ∀ v : E, (∀ i ∈ J, a i v ≤ 0) → h (G v) = 1 →
      f (G v) ≤ f r ∧ (f (G v) = f r → G v = r))
    (hyimage : G y = G x+tau • r)
    (hcap : ∀ z : E, (∀ i, a i z ≤ b i) → ∀ t : ℝ,
      G z = G x+t • r → t ≤ tau) :
    let P := {z : E | ∀ i, a i z ≤ b i}
    let ell := f-(f r) • h
    (G '' {v : E | ∀ i ∈ J, a i v ≤ 0} =
      {w : F | ∃ s : ℝ, 0 ≤ s ∧ ∃ z ∈ P, w = s • (G z-G x)}) ∧
    (∀ z ∈ G '' P, ell z ≤ ell (G x)) ∧
    {z | z ∈ G '' P ∧ ell z = ell (G x)} = segment ℝ (G x) (G y) ∧
    G x ≠ G y ∧ IsExtreme ℝ (G '' P) (segment ℝ (G x) (G y)) ∧
    c (G x) < c (G y) := by sorry
