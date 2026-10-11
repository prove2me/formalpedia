-- Prove2me | Theorems.Thm_PalisConjecture_exists_unique_flow
-- name    : PalisConjecture.exists_unique_flow
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:19:09.257984+00:00
-- url     : https://prove2.me/theorems/2d099930-25cd-41b6-8c44-9aa6093ea122
-- title:
--   Existence and uniqueness of the flow of a $C^r$ vector field on a compact manifold
-- statement:
--   Let $M$ be a compact Hausdorff boundaryless smooth manifold modelled on $\mathbb R^n$, let $r\ge1$, and let $X$ be a $C^r$ vector field on $M$. Then there is exactly one map $\Phi:\mathbb R\times M\to M$ such that, for every $p\in M$, $\Phi_0(p)=p$ and
--   $$\frac{d}{dt}\Phi_t(p)=X\big(\Phi_t(p)\big)\quad\text{for all } t\in\mathbb R.$$
--
--   Vector fields on compact boundaryless manifolds are complete. This guarantees that the flow statements of the mission, which quantify over all flows of $X$, are about the actual flow of $X$ and are not vacuous.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem exists_unique_flow (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : IsCrVectorField r X) :
    ∃! Φ : ℝ → M → M, IsFlowOf X Φ := by
  sorry

end PalisConjecture
