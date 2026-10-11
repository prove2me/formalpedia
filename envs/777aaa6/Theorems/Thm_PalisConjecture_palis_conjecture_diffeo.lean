-- Prove2me | Theorems.Thm_PalisConjecture_palis_conjecture_diffeo
-- name    : PalisConjecture.palis_conjecture_diffeo
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T02:59:25.792339+00:00
-- url     : https://prove2.me/theorems/e83462b2-c2d7-4ab3-8653-12511a9d56fb
-- title:
--   Palis conjecture for diffeomorphisms
-- statement:
--   Let $M$ be a compact, connected, Hausdorff, boundaryless smooth manifold of dimension $n$ (modelled on $\mathbb R^n$), and let $r\ge1$. There is a $C^r$-dense set $D\subset\mathrm{Diff}^r(M)$ such that every $f\in D$ has finitely many attractors $\Lambda_1,\dots,\Lambda_k$ with
--   $$\mathrm{Leb}\Big(M\setminus\bigcup_{i=1}^k B_f(\Lambda_i)\Big)=0.$$
--   Here $B_f(\Lambda)=\{p\in M:\omega_f(p)\subset\Lambda\}$, and an attractor is a set $\Lambda$ with $f(\Lambda)=\Lambda$, having a dense forward orbit, and whose basin has positive Lebesgue measure.
--
--   This is the discrete-time half of the Palis conjecture.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff

namespace PalisConjecture

theorem palis_conjecture_diffeo (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : Set (M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M), IsCrDenseDiffeo r D ∧
      ∀ f ∈ D, HasFiniteAttractorsCoveringAE n (f : M → M) := by
  sorry

end PalisConjecture
