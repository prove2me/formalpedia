-- Prove2me | Theorems.Thm_LeblRA_algebra_closure
-- name    : LeblRA.algebra_closure
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:28.624952+00:00
-- url     : https://prove2.me/theorems/7d214fb2-bbae-4714-bb4f-f7d98dc28eaf
-- title:
--   Proposition 11.7.6 — Closure preserves real and complex function algebras
-- statement:
--   Let $X$ be a compact metric space. For each of the fields $K=\mathbb R$ and $K=\mathbb C$, let $A$ be an algebra of continuous $K$-valued functions on $X$, not necessarily containing the constant function $1$. Then
--   $$
--   \exists B\subseteq C(X,K),\qquad
--   B\text{ is a }K\text{-algebra}\quad\land\quad B=\overline A,
--   $$
--   where closure is taken in the uniform topology.
--
--   This is [Lebl’s Proposition 11.7.6](https://www.jirka.org/ra/html/sec_stoneweier.html): uniform closure preserves the algebraic operations. The real and complex assertions are kept together.
--
--   **Formalization Note.** An algebra contains zero and is closed under addition, pointwise multiplication, and multiplication by every scalar. No point separation, nowhere-vanishing, conjugation closure, or prior closedness is assumed. The Lean carrier equality is exactly equality with topological closure in the continuous-function space, whose compact-open and uniform topologies agree here. Empty compact spaces are included.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Proposition 11.7.6. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem algebra_closure {X : Type*} [MetricSpace X] [CompactSpace X] :
    (∀ A : NonUnitalSubalgebra ℝ C(X, ℝ),
      ∃ B : NonUnitalSubalgebra ℝ C(X, ℝ), (B : Set C(X, ℝ)) = closure (A : Set C(X, ℝ))) ∧
    (∀ A : NonUnitalSubalgebra ℂ C(X, ℂ),
      ∃ B : NonUnitalSubalgebra ℂ C(X, ℂ), (B : Set C(X, ℂ)) = closure (A : Set C(X, ℂ))) := by sorry
end LeblRA
