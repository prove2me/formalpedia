-- Prove2me | Theorems.Thm_Hirsch_polyhedral_summand_endpoint_lifts_and_routes
-- name    : Hirsch.polyhedral_summand_endpoint_lifts_and_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T03:49:55.849982+00:00
-- url     : https://prove2.me/theorems/ab046a79-d0fb-47da-abac-df85c1ace598
-- title:
--   Lift every original polyhedral vertex through a compact summand and transfer route bounds
-- statement:
--   Let P be ANY finite original H-polyhedron in R^d, with arbitrary real linear rows and right-hand sides, and let Q be a nonempty compact convex set. Every actual extreme point u of P admits an extreme point q of Q such that u+q is an actual extreme point of the actual Minkowski sum R=P+Q. No exposing objective, rank, compatible endpoint, or finite vertex list is supplied. The proof derives a unique exposing objective by summing all original rows active at u, then selects an extreme point of the compact maximizing face in Q. Consequently, for any natural B, if every pair of actual extreme points of R has an exposed-edge vertex walk of length at most B, every independently chosen pair of actual extreme points of P has a nondegenerate exposed/extreme-edge vertex walk of length at most B. P need not be bounded, full-dimensional or simple; Q need not be polytopal. Empty active sets, dimension zero, and coincident endpoints are covered. Compactness and nonemptiness of Q and the all-pairs bound on R remain explicit. No short Minkowski completion, bound on its input complexity, arbitrary-projection theorem, algorithmic runtime, or unrestricted Polynomial Hirsch result is asserted.
-- source:
--   Concrete endpoint-surjectivity obligation after accepted #309 (Hirsch.minkowski_summand_exposed_route_contraction, theorem9058b830-964e-4c2d-80d7-e17c68e51cb6). Its entire namespace prefix is reused unchanged from proof66abd8d056b6069a53e983dc7489ee8f1e187cb0, omitting only the old public solution/prints. The finite-margin helper is reused unchanged from the accepted #308 geometry chain. The compact maximizing-face step uses pinned Mathlib KreinMilman.lean and Exposed.lean. Classical polytope diameter contraction is credited to Deza and Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643, Canadian Mathematical Bulletin62(4),2019; this is a formal original-H/compact-summand applicability theorem, not historical priority.

import Mathlib
set_option autoImplicit false

theorem Hirsch.polyhedral_summand_endpoint_lifts_and_routes (d m B : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (Q : Set (Fin d → ℝ)) (hQ : Convex ℝ Q) (hQc : IsCompact Q) (hQne : Q.Nonempty) :
    let P : Set (Fin d → ℝ) := {x | ∀ i, A i x ≤ b i}
    let R : Set (Fin d → ℝ) := {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z}
    (∀ u ∈ P.extremePoints ℝ, ∃ q ∈ Q.extremePoints ℝ, u+q ∈ R.extremePoints ℝ) ∧
    ((∀ z₀ ∈ R.extremePoints ℝ, ∀ z₁ ∈ R.extremePoints ℝ,
      ∃ N : ℕ, N ≤ B ∧ ∃ z : ℕ → (Fin d → ℝ),
        z 0=z₀ ∧ z N=z₁ ∧ (∀ i, i ≤ N → z i ∈ R.extremePoints ℝ) ∧
        ∀ i, i < N → z i ≠ z (i+1) ∧ IsExposed ℝ R (segment ℝ (z i) (z (i+1)))) →
      ∀ u ∈ P.extremePoints ℝ, ∀ v ∈ P.extremePoints ℝ,
      ∃ L : ℕ, L ≤ B ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=u ∧ p L=v ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) := by sorry
