-- Prove2me | Theorems.Thm_Hirsch_two_exception_linear_original_routes
-- name    : Hirsch.two_exception_linear_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T01:56:12.143986+00:00
-- url     : https://prove2.me/theorems/0ad22f42-8283-45ec-87e1-cfaadbe632ea
-- title:
--   Linear original-edge routes with at most two exceptional target rows
-- statement:
--   For any finite real generator family C in ambient dimension d whose convex hull is exactly the original m linear halfspaces, any actual vertices u,v, and a set B of at most two original row labels, assume every target-tight row outside B has at most two values on all actual vertices, one being its boundary value. Construct a route in the original polytope of length at most (m-d)+m. Every visited point is an actual extreme point. Every successive pair is distinct and its entire segment is an extreme subset of the original polytope. Every target row already tight stays tight at each step, including exceptional rows. The remaining affine dimension, original-row incidence count, and route are derived; there is no graph, basis, small-catalogue or cheap-route premise. Redundancies, nonsimple or lower-dimensional hulls, zero dimension and coincident endpoints are allowed. The theorem is a restricted class result, not a uniform Polynomial Hirsch theorem or shortest-path assertion.
-- source:
--   Classical affine-line extremality and planar vertex/row incidence counting, composed with accepted #325 geometric entry and locked strict-ascent proof bodies. The original #325 optional-row-code bound specializes quadratically for two exceptions; this packet proves a linear residual vertex bound by counting actual incidences instead. No historical priority or best-known diameter claim. Accepted #324 remains sharper for at most one exception. Independent affine-roof work #326 and reserved #282/#210 are not used or modified.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.two_exception_linear_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (hB : B.card ≤ 2) (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ (m-d)+m ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
