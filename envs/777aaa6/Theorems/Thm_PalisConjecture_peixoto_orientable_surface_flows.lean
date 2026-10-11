-- Prove2me | Theorems.Thm_PalisConjecture_peixoto_orientable_surface_flows
-- name    : PalisConjecture.peixoto_orientable_surface_flows
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:13:22.100757+00:00
-- url     : https://prove2.me/theorems/bf5b0f39-516b-4b40-8ce9-9602673e0f4a
-- title:
--   Peixoto: finitude of attractors for flows on orientable surfaces
-- statement:
--   Let $M$ be a compact, connected, Hausdorff, boundaryless, **orientable** smooth surface ($\dim M=2$), and let $r\ge1$. There is a $C^r$-dense set $D$ of $C^r$ vector fields on $M$ such that for every $X\in D$ the flow of $X$ has finitely many attractors whose basins cover Lebesgue-almost all of $M$.
--
--   This is the flow version of the Palis conjecture on orientable surfaces. It follows from Peixoto's theorem (1962): Morse–Smale vector fields are open and dense in $\mathfrak X^r(M)$. For a Morse–Smale field the attractors are the sinks and the attracting closed orbits. Every other point lies in the stable set of a saddle, a source or a repelling orbit, and the union of these stable sets is a finite union of points and curves.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology
import Definitions.Def_palis_orientable

open scoped Manifold ContDiff

namespace PalisConjecture

theorem peixoto_orientable_surface_flows {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] (hM : IsOrientable 2 M) (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : Set ((x : M) → TangentSpace (𝓡 2) x), (∀ X ∈ D, IsCrVectorField r X) ∧
      IsCrDenseVF r D ∧
      ∀ X ∈ D, ∀ Φ : ℝ → M → M, IsFlowOf X Φ → FlowHasFiniteAttractorsCoveringAE 2 Φ := by
  sorry

end PalisConjecture
