-- Prove2me | Theorems.Thm_PalisConjecture_sink_is_attractor
-- name    : PalisConjecture.sink_is_attractor
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T03:16:04.149512+00:00
-- url     : https://prove2.me/theorems/6b006391-2bed-4413-9df4-9aacf3578593
-- title:
--   A hyperbolic sink is an attractor
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modelled on $\mathbb R^n$, let $r\ge1$, and let $f$ be a $C^r$ diffeomorphism of $M$ with a fixed point $p$. Let $e$ be a chart of the atlas whose domain contains $p$, and let $A=D(e\circ f\circ e^{-1})(e(p))$ be the derivative of $f$ at $p$ in this chart. If
--   $$\|A^N\|<1\quad\text{for some } N\ge0$$
--   (equivalently, every eigenvalue of $A$ has modulus $<1$), then $\{p\}$ is an attractor of $f$.
--
--   This is the basic example of an attractor and shows that the attractor definition is satisfied by hyperbolic sinks, whose basins contain an open neighbourhood of $p$.
--
--   **Formalization Note** The operator norm is taken with respect to the Euclidean norm on $\mathbb R^n$.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem sink_is_attractor (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M) (p : M) (hp : f p = p)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (hpe : p ∈ e.source)
    (hsink : ∃ N : ℕ, ‖(fderiv ℝ (e ∘ f ∘ e.symm) (e p)) ^ N‖ < 1) :
    IsAttractor n (f : M → M) {p} := by
  sorry

end PalisConjecture
