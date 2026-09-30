-- Prove2me | Theorems.Thm_Hirsch_projected_minimal_face_from_fibre_duals
-- name    : Hirsch.projected_minimal_face_from_fibre_duals
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T21:06:38.005026+00:00
-- url     : https://prove2.me/theorems/2e10b83d-9a75-4d41-a7e5-95a483d787aa
-- title:
--   Construct the exact minimal exposed image face and kernel direction tests from original-row fibre duals
-- statement:
--   Let P be given by finitely many real linear inequalities a_i(z)<=b_i and let G be linear. A feasible anchor x is tight exactly on a selected finite row set J. For every selected row, suppose nonnegative original-row coefficients and an image linear functional give the exact primal-dual identities certifying maximum slack zero on the fibre Gz=Gx. Then construct an image linear functional exposing exactly G(H), where H is the original equality face on J. This is an actual extreme subset and the smallest extreme subset of GP containing Gx. For every image submodule W, every difference Gz-Gx for z in H lies in W exactly when G sends every vector in the selected-row kernel into W. The exposing objective, minimality and all-submodule direction equivalence are conclusions. No image exposer, compactness, bounded preimage, source vertex or source edge is assumed. The finite strict anchor and exact dual identities are checkable data; discovery of these witnesses and the generic image-edge algorithm are separate executable/mathematical components, not silently Lean-extracted. No bound on the number of image edges or general Polynomial Hirsch conclusion is asserted.
-- source:
--   Classical finite polyhedral duality and minimal-face geometry, proved directly from original-row identities and finite strict slacks. The support-extreme helper reuses accepted PR #246 with bound-variable/namespace renaming. The actual minimum finite radius uses the same method as accepted #245. This continuation constructs the image exposing normal by summing fibre-row duals, proves minimality by feasible backward perturbations, and binds the full face direction tests to the selected-row kernel. No historical novelty or strongly polynomial runtime claim.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.projected_minimal_face_from_fibre_duals
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E) (lam : ι → ι → ℝ) (psi : ι → F →ₗ[ℝ] ℝ)
    (hx : ∀ j, a j x ≤ b j) (hJ : ∀ j ∈ J, a j x = b j)
    (hstrict : ∀ j, j ∉ J → a j x < b j)
    (hlam : ∀ i ∈ J, ∀ j, 0 ≤ lam i j)
    (hnormal : ∀ i ∈ J, -a i = (∑ j, lam i j • a j) + (psi i).comp G)
    (hvalue : ∀ i ∈ J, -b i = (∑ j, lam i j*b j) + psi i (G x)) :
    let P := {z : E | ∀ i, a i z ≤ b i}
    let H := {z : E | (∀ i, a i z ≤ b i) ∧ ∀ i ∈ J, a i z = b i}
    ∃ f : F →ₗ[ℝ] ℝ,
      (∀ y ∈ G '' P, f y ≤ f (G x)) ∧
      {y | y ∈ G '' P ∧ f y = f (G x)} = G '' H ∧
      IsExtreme ℝ (G '' P) (G '' H) ∧
      (∀ D : Set F, IsExtreme ℝ (G '' P) D → G x ∈ D → G '' H ⊆ D) ∧
      (∀ W : Submodule ℝ F,
        (∀ z ∈ H, G z-G x ∈ W) ↔
        (∀ v : E, (∀ i ∈ J, a i v = 0) → G v ∈ W)) := by sorry
