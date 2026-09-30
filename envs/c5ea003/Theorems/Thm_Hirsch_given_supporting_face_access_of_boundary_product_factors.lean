-- Prove2me | Theorems.Thm_Hirsch_given_supporting_face_access_of_boundary_product_factors
-- name    : Hirsch.given_supporting_face_access_of_boundary_product_factors
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T21:03:28.107558+00:00
-- url     : https://prove2.me/theorems/cf9699ad-34c6-4202-8b4a-10177c844813
-- title:
--   Prescribed supporting-face access through affine products of small factors
-- statement:
--   Fix a describing row i tight at a vertex v of a bounded n-row H-polytope P in R^d and a source vertex u. Suppose for every edge x-z entering the prescribed equality face i, there is an injective affine chart of a finite Cartesian product of bounded H-polytopes whose image is an extreme subset of P containing u and x. The factors may depend on the crossing. Each factor dimension is at most r; the sum of their describing-row counts is at most M. Then an extreme point on the SAME prescribed row i is reached from u in M*2^(max(r-3,0))+1 padded edge steps. Total face dimension and residual rank are not bounded by r. If r<=3 the budget is M+1. The empty product is allowed. No separation or distinctness hypothesis is needed. This does not assert that arbitrary common-source faces have a small-factor product structure and does not prove an unrestricted polynomial Hirsch bound.
-- source:
--   Working derivation, jjoshua2/prove2me-work branch chatgpt/boundary-product-access. Standard additive product-diameter construction applied locally to first-contact faces. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.given_supporting_face_access_of_boundary_product_factors
    (d n M r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i)
    (hfactor : ∀ x z, Adj (Hpoly a b) x z →
      ⟪a i, x⟫ ≠ b i → ⟪a i, z⟫ = b i →
      ∃ (m : ℕ) (ds ns : Fin m → ℕ)
        (aa : (k : Fin m) → Fin (ns k) → EuclideanSpace ℝ (Fin (ds k)))
        (bb : (k : Fin m) → Fin (ns k) → ℝ)
        (f : ((k : Fin m) → EuclideanSpace ℝ (Fin (ds k))) →ᵃ[ℝ]
          EuclideanSpace ℝ (Fin d)),
        Function.Injective f ∧
        IsExtreme ℝ (Hpoly a b) (f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k))) ∧
        u ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        x ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        (∀ k, Bornology.IsBounded (Hpoly (aa k) (bb k))) ∧
        (∀ k, ds k ≤ r) ∧ (∑ k, ns k) ≤ M) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (M * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < M * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry
