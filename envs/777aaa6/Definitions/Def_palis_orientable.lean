-- Prove2me | Definitions.Def_palis_orientable
-- name    : palis_orientable
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:54:44.468996+00:00
-- url     : https://prove2.me/theorems/7f2d87aa-a4c1-4617-aa51-04ba9332b784
-- title:
--   Orientable manifolds
-- statement:
--   A smooth manifold $M$ modelled on $\mathbb R^n$ is **orientable** if there is a family $\mathcal A$ of charts from the maximal $C^\infty$ atlas of $M$ whose domains cover $M$ and whose transition maps have positive Jacobian determinant:
--   $$\det D(e'\circ e^{-1})(y)>0\quad\text{for all } e,e'\in\mathcal A \text{ and } y\in e(U_e\cap U_{e'}).$$
--
--   This hypothesis is used in Peixoto's theorem on flows on surfaces.
--
--   **Formalization Note** The maximal atlas is `IsManifold.maximalAtlas (𝓡 n) ∞ M`. The determinant is that of the Fréchet derivative, viewed as a linear map.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib

/-!
# Orientable manifolds
-/

namespace PalisConjecture

open scoped Manifold ContDiff

/-- `M` is orientable: there is a family of charts from the maximal smooth atlas covering `M`
whose transition maps all have positive Jacobian determinant. -/
def IsOrientable (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  ∃ A ⊆ IsManifold.maximalAtlas (𝓡 n) ∞ M,
    (∀ x : M, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ y ∈ e.target ∩ e.symm ⁻¹' e'.source,
      0 < LinearMap.det (fderiv ℝ (e' ∘ e.symm) y : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))

end PalisConjecture


