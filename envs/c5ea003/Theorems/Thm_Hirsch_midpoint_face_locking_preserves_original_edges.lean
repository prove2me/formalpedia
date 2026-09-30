-- Prove2me | Theorems.Thm_Hirsch_midpoint_face_locking_preserves_original_edges
-- name    : Hirsch.midpoint_face_locking_preserves_original_edges
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T22:45:25.617021+00:00
-- url     : https://prove2.me/theorems/d67aa510-011e-4a33-bbc3-87ba15d20e15
-- title:
--   Construct minimal common image faces and transfer face-locked pivots to original edges
-- statement:
--   Given a finite original H-system, a linear image, two feasible image endpoints, and exact original-row zero-slack fibre duals at a strict anchor over their midpoint, construct the least convex extreme image face containing both endpoints. Prove it is an entire exposed slice, contains the endpoints, and is contained in every convex extreme subset containing them. Any nondegenerate segment extreme in this constructed face is extreme in the ORIGINAL image and remains inside every common target face. No source adjacency, image facet list, compactness, or minimality/exposure oracle is assumed. The input edge-in-the-restricted-face witness is explicitly supplied by the previously accepted normalized-tangent edge theorem; this theorem does not manufacture a route-length bound. Convexity of common faces is essential because IsExtreme alone need not be convex.
-- source:
--   Reuses accepted #247 projected_minimal_face_from_fibre_duals source byte-for-byte except root theorem/axiom-print name. New midpoint, convex-image-face, and edge-transfer composition for adaptive face locking; classical minimal-face geometry, no novelty claim. #248 supplies the restricted-face edge witnesses without changing its source.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.midpoint_face_locking_preserves_original_edges
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E) (u v : F)
    (lam : ι → ι → ℝ) (psi : ι → F →ₗ[ℝ] ℝ)
    (hx : ∀ j, a j x ≤ b j) (hJ : ∀ j ∈ J, a j x = b j)
    (hstrict : ∀ j, j ∉ J → a j x < b j)
    (hlam : ∀ i ∈ J, ∀ j, 0 ≤ lam i j)
    (hnormal : ∀ i ∈ J, -a i = (∑ j, lam i j • a j) + (psi i).comp G)
    (hvalue : ∀ i ∈ J, -b i = (∑ j, lam i j*b j) + psi i (G x))
    (hu : u ∈ G '' {z : E | ∀ j, a j z ≤ b j})
    (hv : v ∈ G '' {z : E | ∀ j, a j z ≤ b j})
    (hmid : G x = (1/2 : ℝ) • u+(1/2 : ℝ) • v) :
    let M := G '' {z : E | ∀ j, a j z ≤ b j}
    let H := G '' {z : E | (∀ j, a j z ≤ b j) ∧ ∀ j ∈ J, a j z = b j}
    ∃ f : F →ₗ[ℝ] ℝ,
      (∀ y ∈ M, f y ≤ f (G x)) ∧
      {y | y ∈ M ∧ f y = f (G x)} = H ∧
      Convex ℝ H ∧ IsExtreme ℝ M H ∧ u ∈ H ∧ v ∈ H ∧
      (∀ D : Set F, Convex ℝ D → IsExtreme ℝ M D → u ∈ D → v ∈ D → H ⊆ D) ∧
      (∀ w : F, u ≠ w → IsExtreme ℝ H (segment ℝ u w) →
        IsExtreme ℝ M (segment ℝ u w) ∧
        ∀ D : Set F, Convex ℝ D → IsExtreme ℝ M D → u ∈ D → v ∈ D →
          segment ℝ u w ⊆ D) := by sorry
