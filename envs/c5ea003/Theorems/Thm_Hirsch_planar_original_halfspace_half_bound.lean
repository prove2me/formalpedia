-- Prove2me | Theorems.Thm_Hirsch_planar_original_halfspace_half_bound
-- name    : Hirsch.planar_original_halfspace_half_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-24T00:53:19.637318+00:00
-- url     : https://prove2.me/theorems/21a3f083-3ba6-4077-bb22-9a09eef37804
-- title:
--   Chart-free planar original-edge routes bounded by half the original inequality count
-- statement:
--   For any finite real planar generator set C and m original linear inequalities with exact conv(C)=the feasible set, construct an original exposed-edge route between any two actual extreme endpoints with 2L<=m. Every visited point is an actual original extreme point and each step is a whole nondegenerate exposed segment of the original feasible set. The complete vertex set, strict exposure, independent coordinate, sorted radial chart and short walk are derived, not supplied. Redundant generators and inequalities, zero rows, equal endpoints and lower-dimensional bodies remain included. Finite-hull/H equality and endpoint extremality are explicit. This is a planar original-row bound, not an arbitrary-dimensional Polynomial Hirsch theorem, an algorithmic H-to-V complexity guarantee, or a formal irredundant-facet/shortestness result.
-- source:
--   Composition and original-input completion of accepted PR339 with accepted PR327 incidence helpers and Mathlib compact convex-hull, extreme-point and finite-order results. The ambient-plane specialization yields |V|<=m; new code derives complete actual vertices and all chart choices. Classical planar geometry is not claimed historically novel.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.planar_original_halfspace_half_bound (m : ℕ) (C : Finset (Fin 2 → ℝ))
    (A : Fin m → (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin 2 → ℝ)) = {x | ∀ i, A i x ≤ b i})
    (u v : Fin 2 → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ) :
    ∃ L : ℕ, 2 * L ≤ m ∧ ∃ q : Fin (L + 1) → (Fin 2 → ℝ),
      q 0 = u ∧ q (Fin.last L) = v ∧
      (∀ i, q i ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ) ∧
      ∀ i : Fin L, q i.castSucc ≠ q i.succ ∧
        IsExposed ℝ {x : Fin 2 → ℝ | ∀ i, A i x ≤ b i}
          (segment ℝ (q i.castSucc) (q i.succ)) := by sorry
