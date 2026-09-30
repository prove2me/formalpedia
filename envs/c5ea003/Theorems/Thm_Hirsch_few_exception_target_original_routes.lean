-- Prove2me | Theorems.Thm_Hirsch_few_exception_target_original_routes
-- name    : Hirsch.few_exception_target_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T00:49:58.895594+00:00
-- url     : https://prove2.me/theorems/e8842064-8672-4cea-9e53-6f6bedf68b8f
-- title:
--   Original edge routes with a bounded number of unrestricted target rows
-- statement:
--   For a finite real generator set C whose entire convex hull equals the m original linear halfspaces in ambient dimension d, and actual extreme endpoints u,v, let B be any finite set of original labels. Assume every target-tight row outside B takes at most its boundary value and one other value on actual vertices. Construct an original ordinary-edge walk through actual vertices, preserving every acquired target row, with length at most m-d+((m+1)^|B|-1). Derive all retained-face geometry, active-row selection, residual dimension at most |B|, residual vertex code count and the whole route. No graph, rank, small catalogue, improving-neighbor, connectivity or bounded-route oracle is assumed. The polynomial degree depends on |B|; this is not uniform Polynomial Hirsch, shortestness, one-row acquisition per edge, all-facet nonrevisiting or polynomial-time computation.
-- source:
--   Parameterized finite-dimensional row-basis counting and original-edge ascent, continuing accepted #323 and #324. The accepted #323 844-line namespace prefix is reused byte-for-byte without its public root. New geometry and code construction derive the residual vertex count from original active rows rather than scalar-level inventories. Classical basis selection and convex polytope edge geometry are credited in explanation.md; no historical-priority or best-bound claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.few_exception_target_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ m-d+((m+1)^B.card-1) ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
