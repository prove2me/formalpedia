-- Prove2me | Theorems.Thm_ZeroOneExpansion_fact_3
-- name    : ZeroOneExpansion.fact_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:21:19.335445+00:00
-- url     : https://prove2.me/theorems/4b70e80c-415e-405e-b845-1300348689aa
-- title:
--   Fact 3 — the vertices of a 0/1-polytope are its generators
-- statement:
--   If $\emptyset\neq X\subseteq\{0,1\}^d$, then the vertex set of $\operatorname{conv}(X)$ is exactly $X$:
--   $$V(\operatorname{conv}(X))=X.$$
--   Here a vertex is a point $x$ for which $\{x\}$ is a face.
--
--   No Boolean generator of a 0/1-polytope is redundant; this gives the vertex set $V_n$ of $P_n$.
--
--   Differences from the source:
--   - encoding: V(P), the set of zero-dimensional faces → {x | IsExposed ℝ P {x}}; reason: a zero-dimensional face is a singleton face
--   - encoding: X ⊆ {0,1}^d → X a Finset of 0/1 vectors; reason: every subset of {0,1}^d is finite
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Fact 3, p.3

import Mathlib
import Definitions.Def_ZeroOneExpansion_IsAdj

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Fact 3** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.3). If `∅ ≠ X ⊆ {0, 1}^d`, then `V(conv(X)) = X`.

**Formalization Note** `V(P)` is the set of points `x` with `{x}` a face of `P` (`IsVertexOf`,
i.e. `IsExposed ℝ P {x}`, the predicate of `Grunbaum2003.PolytopeVertex`). `X` is a `Finset`; every
subset of `{0,1}^d` is finite. -/
theorem fact_3 {d : ℕ} (X : Finset (Fin d → ℝ)) (hX : X.Nonempty)
    (h01 : ∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1) :
    {x | IsVertexOf (convexHull ℝ (X : Set (Fin d → ℝ))) x} = (X : Set (Fin d → ℝ)) := by sorry

end ZeroOneExpansion
