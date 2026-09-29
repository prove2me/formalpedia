-- Prove2me | Theorems.Thm_LeblRA_complex_stone_weierstrass
-- name    : LeblRA.complex_stone_weierstrass
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:59.575104+00:00
-- url     : https://prove2.me/theorems/56215489-7feb-441b-9a5e-ba1dfc63bfac
-- title:
--   Theorem 11.7.16 — Complex non-unital Stone–Weierstrass theorem
-- statement:
--   Let $X$ be a compact metric space, and let $A$ be a complex algebra of continuous complex-valued functions on $X$, not necessarily containing the constant function $1$. Suppose that
--   $$
--   \forall x\ne y\;\exists g\in A,\quad g(x)\ne g(y),
--   \qquad
--   \forall x\in X\;\exists g\in A,\quad g(x)\ne0,
--   $$
--   and that $A$ is closed under pointwise conjugation:
--   $$
--   g\in A\Longrightarrow \overline g\in A.
--   $$
--   Then
--   $$
--   \overline A=C(X,\mathbb C).
--   $$
--
--   The conclusion gives uniform approximation of every continuous complex-valued function by members of $A$. This is the full non-unital complex Stone–Weierstrass theorem, [Lebl’s Theorem 11.7.16](https://www.jirka.org/ra/html/sec_stoneweier.html).
--
--   **Formalization Note.** The algebra includes zero but does not assume a unit. Point separation, nowhere-vanishing, and conjugation closure are distinct explicit hypotheses. On continuous complex-valued maps, the Lean star operation is pointwise conjugation. Closure is the uniform closure on the compact domain; empty compact spaces are included.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Theorem 11.7.16. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem complex_stone_weierstrass {X : Type*} [MetricSpace X] [CompactSpace X]
    (A : NonUnitalSubalgebra ℂ C(X, ℂ))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y)
    (nv : ∀ x : X, ∃ g ∈ A, g x ≠ 0)
    (adj : ∀ g ∈ A, star g ∈ A) :
    closure (A : Set C(X, ℂ)) = Set.univ := by sorry
end LeblRA
