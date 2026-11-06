-- Prove2me | Theorems.Thm_ZeroOneExpansion_fact_2
-- name    : ZeroOneExpansion.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:59.589695+00:00
-- url     : https://prove2.me/theorems/875c38ab-36cb-4caf-9a8c-02d656692984
-- title:
--   Fact 2 — faces of $\operatorname{conv}(X)$ from the generating set
-- statement:
--   Let $X\subseteq\mathbb R^d$ be finite and nonempty, and let $c\in\mathbb R^d$. Then the face of $\operatorname{conv}(X)$ exposed by $c$ is the convex hull of the maximizers of $c\cdot x$ over $X$:
--   $$F_c(\operatorname{conv}(X))=\operatorname{conv}\{x\in X: c\cdot x=\max_{z\in X}c\cdot z\}.$$
--
--   This identifies faces of a polytope directly from a finite generating set; it is used in Facts 3 and 6.
--
--   Differences from the source:
--   - encoding: F_c(P) = {x ∈ P : c·x = max_{y∈P} c·y} → the maximizer set {x ∈ P | ∀ y ∈ P, c·y ≤ c·x} (exposedFace); reason: equal whenever the maximum exists, as on every polytope
--   - encoding: {x ∈ X : c·x = max_{z∈X} c·z} → {x ∈ X | ∀ z ∈ X, c·z ≤ c·x}; reason: the same set for finite nonempty X
--   - encoding: X ⊆ ℝ^d finite → X a Finset; reason: the same sets
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Fact 2, p.3

import Mathlib
import Definitions.Def_ZeroOneExpansion_exposedFace

set_option autoImplicit false

open Matrix

namespace ZeroOneExpansion

/-- **Fact 2** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.3). Let `X ⊆ ℝ^d` be finite and nonempty and `c ∈ ℝ^d`. Then
`F_c(conv(X)) = conv{x ∈ X : c · x = max_{z∈X} c · z}`.

**Formalization Note** `F_c` is `exposedFace · (fun x => c ⬝ᵥ x)`, the maximizer set of `x ↦ c · x`.
The maximizers of `c · x` over the finite nonempty `X` are written `∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x`. -/
theorem fact_2 {d : ℕ} (X : Finset (Fin d → ℝ)) (hX : X.Nonempty) (c : Fin d → ℝ) :
    exposedFace (convexHull ℝ (X : Set (Fin d → ℝ))) (fun x => c ⬝ᵥ x) =
      convexHull ℝ {x | x ∈ X ∧ ∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x} := by sorry

end ZeroOneExpansion
