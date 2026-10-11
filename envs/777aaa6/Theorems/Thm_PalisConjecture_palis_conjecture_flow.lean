-- Prove2me | Theorems.Thm_PalisConjecture_palis_conjecture_flow
-- name    : PalisConjecture.palis_conjecture_flow
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:01:34.874846+00:00
-- url     : https://prove2.me/theorems/ef745b80-761a-4eb1-b7c6-9c262790c8ff
-- title:
--   Palis conjecture for flows
-- statement:
--   Let $M$ be a compact, connected, Hausdorff, boundaryless smooth manifold of dimension $n$ (modelled on $\mathbb R^n$), and let $r\ge1$. There is a $C^r$-dense set $D$ of $C^r$ vector fields on $M$ such that for every $X\in D$ the flow $\Phi$ of $X$ has finitely many attractors $\Lambda_1,\dots,\Lambda_k$ with
--   $$\mathrm{Leb}\Big(M\setminus\bigcup_{i=1}^k B_\Phi(\Lambda_i)\Big)=0.$$
--   Here $B_\Phi(\Lambda)=\{p:\omega_\Phi(p)\subset\Lambda\}$, with $\omega_\Phi(p)$ the accumulation points of $\Phi_t(p)$ as $t\to+\infty$. An attractor is a set invariant under every $\Phi_t$, with a dense forward orbit, whose basin has positive Lebesgue measure.
--
--   This is the continuous-time half of the Palis conjecture.
--
--   **Formalization Note** The statement holds for every global flow $\Phi$ of $X$, i.e. $\Phi_0=\mathrm{id}$ and each orbit is an integral curve of $X$.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem palis_conjecture_flow (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : Set ((x : M) → TangentSpace (𝓡 n) x), (∀ X ∈ D, IsCrVectorField r X) ∧
      IsCrDenseVF r D ∧
      ∀ X ∈ D, ∀ Φ : ℝ → M → M, IsFlowOf X Φ → FlowHasFiniteAttractorsCoveringAE n Φ := by
  sorry

end PalisConjecture
