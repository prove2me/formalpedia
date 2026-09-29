-- Prove2me | Theorems.Thm_LeblRA_real_stone_weierstrass
-- name    : LeblRA.real_stone_weierstrass
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:49.075907+00:00
-- url     : https://prove2.me/theorems/e353e340-d8e4-44c2-b343-c1b2a8247318
-- title:
--   Theorem 11.7.12 — Real non-unital Stone–Weierstrass theorem
-- statement:
--   Let $X$ be a compact metric space, and let $A$ be a real algebra of continuous real-valued functions on $X$, not necessarily containing the constant function $1$. Assume
--   $$
--   \forall x\ne y\;\exists g\in A,\quad g(x)\ne g(y),
--   \qquad
--   \forall x\in X\;\exists g\in A,\quad g(x)\ne0.
--   $$
--   Then
--   $$
--   \overline A=C(X,\mathbb R).
--   $$
--
--   Equivalently, for every $f\in C(X,\mathbb R)$ and every $\varepsilon>0$, some $g\in A$ satisfies $|g(x)-f(x)|<\varepsilon$ for all $x\in X$. This is the real non-unital density result in [Lebl’s Theorem 11.7.12](https://www.jirka.org/ra/html/sec_stoneweier.html).
--
--   **Formalization Note.** The algebra contains zero and is closed under addition, multiplication, and real scalar multiplication. Nowhere-vanishing remains an explicit hypothesis; no single everywhere nonzero element is assumed. Closure is taken in the continuous-function space, where compact-open and uniform convergence agree. Empty compact spaces are allowed.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Theorem 11.7.12. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem real_stone_weierstrass {X : Type*} [MetricSpace X] [CompactSpace X]
    (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y)
    (nv : ∀ x : X, ∃ g ∈ A, g x ≠ 0) :
    closure (A : Set C(X, ℝ)) = Set.univ := by sorry
end LeblRA
