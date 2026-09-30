-- Prove2me | Theorems.Thm_Hirsch_three_exception_quadratic_original_routes
-- name    : Hirsch.three_exception_quadratic_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T02:39:14.552859+00:00
-- url     : https://prove2.me/theorems/c31f1378-cca6-46b6-8bc5-c550b25df4f1
-- title:
--   Quadratic original-edge routes with at most three exceptional target rows
-- statement:
--   For a finite real family C in ambient dimension d whose convex hull equals the original m halfspaces, actual extreme endpoints u,v, and at most three exceptional original row labels B, assume every target-tight row outside B has its boundary value and at most one other value on all actual vertices. Construct a route through actual original extreme points of length at most (m-d)+m*m. Every consecutive pair is distinct, its entire segment is IsExtreme in the original halfspace body, and every acquired target row stays tight. Residual dimension, nonzero-restriction slice bounds, incidence counts and the actual route are derived; no graph, basis, residual rank, small catalogue or cheap route is supplied. Exact H/hull equality and the outside-B two-level condition are explicit structural assumptions. Redundant rows/generators, nonsimple/lower-dimensional hulls, dimension zero, coincident endpoints, empty B and non-target exceptions are included. This is not a uniform Polynomial Hirsch theorem, shortestness, all-facet nonrevisiting or an efficient H-to-V claim.
-- source:
--   Formal extension of accepted #327 planar original-row incidence geometry and #325 good-row entry/locked-ascent arguments. The entire accepted #327 namespace prefix is reused unchanged, omitting only its old public solution and axiom-print requests. New code transports a three-dimensional nonzero row slice into a planar ambient submodule, applies the actual planar incidence bound, and double-counts spatial incidences. This improves the cubic three-exception optional-slot specialization to a quadratic formal bound. Classical finite-dimensional and convex geometry; no historical priority, best-known three-dimensional diameter bound or unrestricted conjecture claim. #326 independent affine-roof work is not used or changed.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.three_exception_quadratic_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (hB : B.card ≤ 3) (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ (m-d)+m*m ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
