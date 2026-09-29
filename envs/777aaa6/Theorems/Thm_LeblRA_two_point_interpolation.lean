-- Prove2me | Theorems.Thm_LeblRA_two_point_interpolation
-- name    : LeblRA.two_point_interpolation
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:39.580139+00:00
-- url     : https://prove2.me/theorems/5b70cb7f-5611-4add-ba9b-8a321dd60418
-- title:
--   Proposition 11.7.11 — Two-point interpolation in a non-unital function algebra
-- statement:
--   Let $X$ be an arbitrary set, and let $K$ be either $\mathbb R$ or $\mathbb C$. Let $A$ be a $K$-algebra of functions $X\to K$, not necessarily containing $1$. Suppose that $A$ separates points and vanishes nowhere:
--   $$
--   \forall x\ne y\;\exists g\in A,\quad g(x)\ne g(y),
--   \qquad
--   \forall x\in X\;\exists g\in A,\quad g(x)\ne0.
--   $$
--   Then arbitrary values can be prescribed at two distinct points:
--   $$
--   \forall x\ne y\;\forall c,d\in K\;\exists f\in A,\qquad
--   f(x)=c\quad\land\quad f(y)=d.
--   $$
--
--   This is [Lebl’s Proposition 11.7.11](https://www.jirka.org/ra/html/sec_stoneweier.html), with both scalar fields included in one statement.
--
--   **Formalization Note.** There is no topology, continuity, compactness, or nonemptiness assumption on $X$. The nonvanishing witness may depend on the point. The algebra includes zero; the interpolant is not required to be unique, and either prescribed value may be zero.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Proposition 11.7.11. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem two_point_interpolation (X : Type*) :
    (∀ A : NonUnitalSubalgebra ℝ (X → ℝ),
      (∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y) →
      (∀ x : X, ∃ g ∈ A, g x ≠ 0) →
      ∀ x y : X, x ≠ y → ∀ c d : ℝ, ∃ f ∈ A, f x = c ∧ f y = d) ∧
    (∀ A : NonUnitalSubalgebra ℂ (X → ℂ),
      (∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y) →
      (∀ x : X, ∃ g ∈ A, g x ≠ 0) →
      ∀ x y : X, x ≠ y → ∀ c d : ℂ, ∃ f ∈ A, f x = c ∧ f y = d) := by sorry
end LeblRA
