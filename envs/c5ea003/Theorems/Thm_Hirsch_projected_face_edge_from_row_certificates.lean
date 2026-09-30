-- Prove2me | Theorems.Thm_Hirsch_projected_face_edge_from_row_certificates
-- name    : Hirsch.projected_face_edge_from_row_certificates
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T15:34:17.17156+00:00
-- url     : https://prove2.me/theorems/8c81d5ed-3389-4b7f-a509-c34b7ccbb3a7
-- title:
--   Original-row quotient certificates expose genuine image edges with arbitrary fibres
-- statement:
--   For a finite real H-polyhedron and a linear image map, finite original-row identities prove an entire exposed image edge without assuming source adjacency, source vertices, boundedness, or one-dimensional source faces. A strictly positive exposing row combination, a rank-one quotient identity checked on finitely many columns, and sharp endpoint inequalities prove that the whole image supporting slice is the nondegenerate segment between the supplied projected endpoints. Its actual Mathlib extreme-set property is concluded. Certificate discovery and uniform path-length bounds are not assumed or concluded.
-- source:
--   Classical support-face and finite linear algebra, formalized directly. Uses actual Mathlib IsExtreme and segment definitions, matching Definitions.Def_Hirsch_model adjacency. No new classical novelty, projection-diameter theorem, source-edge hypothesis or support-slice oracle is asserted. Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Exposed.html

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem projected_face_edge_from_row_certificates {d p m r : ℕ}
    (a : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (G : (Fin d → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (f : (Fin p → ℝ) →ₗ[ℝ] ℝ) (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (row : Fin r → Fin m) (lam : Fin r → ℝ) (w : Fin r → (Fin p → ℝ))
    (lower upper : Fin m → ℝ) (lowerEq upperEq : Fin r → ℝ)
    (x y : Fin d → ℝ)
    (hx : ∀ i, a i x ≤ b i) (hy : ∀ i, a i y ≤ b i)
    (hxJ : ∀ j, a (row j) x = b (row j)) (hyJ : ∀ j, a (row j) y = b (row j))
    (hne : G x ≠ G y) (hφ : φ y - φ x = 1)
    (hlam : ∀ j, 0 < lam j)
    (hexpose : f.comp G = ∑ j, lam j • a (row j))
    (hline : ∀ i, G (Pi.single i (1 : ℝ)) =
      φ (Pi.single i (1 : ℝ)) • (G y - G x) +
        ∑ j, a (row j) (Pi.single i (1 : ℝ)) • w j)
    (hlower : ∀ i, 0 ≤ lower i) (hupper : ∀ i, 0 ≤ upper i)
    (hlform : -φ = (∑ i, lower i • a i) + ∑ j, lowerEq j • a (row j))
    (huform : φ = (∑ i, upper i • a i) + ∑ j, upperEq j • a (row j))
    (hlsharp : -φ x = (∑ i, lower i * b i) + ∑ j, lowerEq j * b (row j))
    (husharp : φ y = (∑ i, upper i * b i) + ∑ j, upperEq j * b (row j)) :
    let P := {z : Fin d → ℝ | ∀ i, a i z ≤ b i}
    let β := ∑ j, lam j * b (row j)
    (∀ z ∈ G '' P, f z ≤ β) ∧
      {z | z ∈ G '' P ∧ f z = β} = segment ℝ (G x) (G y) ∧
      G x ≠ G y ∧ IsExtreme ℝ (G '' P) (segment ℝ (G x) (G y)) := by sorry
end Hirsch
