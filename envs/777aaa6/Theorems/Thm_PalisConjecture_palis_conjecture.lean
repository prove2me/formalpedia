-- Prove2me | Theorems.Thm_PalisConjecture_palis_conjecture
-- name    : PalisConjecture.palis_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:22:41.852599+00:00
-- url     : https://prove2.me/theorems/371298dc-3d55-4f48-a968-e362c0d1c380
-- title:
--   Palis conjecture: denseness of finitude of attractors
-- statement:
--   Let $M$ be a compact, connected, Hausdorff, boundaryless smooth manifold of dimension $n$ (modelled on $\mathbb R^n$), and let $r\ge1$ be an integer.
--
--   1. (Diffeomorphisms) There is a $C^r$-dense set $D\subset\mathrm{Diff}^r(M)$ such that every $f\in D$ has finitely many attractors $\Lambda_1,\dots,\Lambda_k$ whose basins cover Lebesgue-almost all of $M$:
--   $$\mathrm{Leb}\Big(M\setminus\bigcup_{i=1}^k B_f(\Lambda_i)\Big)=0.$$
--   2. (Flows) There is a $C^r$-dense set $D\subset\mathfrak X^r(M)$ of $C^r$ vector fields such that, for every $X\in D$, the flow $\Phi$ of $X$ has finitely many attractors whose basins cover Lebesgue-almost all of $M$.
--
--   Here an attractor is an invariant, transitive set whose basin $B(\Lambda)=\{p:\omega(p)\subset\Lambda\}$ has positive Lebesgue measure.
--
--   This is the conjecture of J. Palis as stated on the Open Problem Garden. It replaces the false hope that hyperbolic systems are dense by a statistical description of a dense set of systems.
--
--   **Formalization Note** Density is sequential $C^r$ density (`IsCrDenseDiffeo`, `IsCrDenseVF`). The flow part quantifies over every global flow of $X$; such a flow exists and is unique (see the flow-existence milestone).
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem palis_conjecture (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (r : ℕ) (hr : 1 ≤ r) :
    (∃ D : Set (M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M), IsCrDenseDiffeo r D ∧
        ∀ f ∈ D, HasFiniteAttractorsCoveringAE n (f : M → M)) ∧
    (∃ D : Set ((x : M) → TangentSpace (𝓡 n) x), (∀ X ∈ D, IsCrVectorField r X) ∧
        IsCrDenseVF r D ∧
        ∀ X ∈ D, ∀ Φ : ℝ → M → M, IsFlowOf X Φ → FlowHasFiniteAttractorsCoveringAE n Φ) := by
  sorry

end PalisConjecture
