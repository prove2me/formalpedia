-- Prove2me | Theorems.Thm_PalisConjecture_palis_conjecture_circle
-- name    : PalisConjecture.palis_conjecture_circle
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:08:15.463179+00:00
-- url     : https://prove2.me/theorems/67d15a6d-bd11-4e74-92c9-7adf521dc0c8
-- title:
--   Palis conjecture for circle diffeomorphisms
-- statement:
--   Let $M$ be a compact, connected, Hausdorff, boundaryless smooth manifold of dimension $1$ (that is, a circle), and let $r\ge1$. There is a $C^r$-dense set $D\subset\mathrm{Diff}^r(M)$ such that every $f\in D$ has finitely many attractors whose basins cover Lebesgue-almost all of $M$.
--
--   This is the one-dimensional case of the Palis conjecture. It is classical: Morse–Smale diffeomorphisms of the circle, whose periodic points are finitely many and all hyperbolic, are $C^r$-dense, and for them the attracting periodic orbits are the attractors.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem palis_conjecture_circle {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (𝓡 1) ∞ M] (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : Set (M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 1, 𝓡 1⟯ M), IsCrDenseDiffeo r D ∧
      ∀ f ∈ D, HasFiniteAttractorsCoveringAE 1 (f : M → M) := by
  sorry

end PalisConjecture
