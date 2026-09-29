-- Prove2me | Definitions.Def_fenchelBiconjugate
-- name    : fenchelBiconjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-11T21:37:47.838781+00:00
-- url     : https://prove2.me/theorems/50b9a27c-4896-41bc-9e4e-5e4ec07a00bd
-- title:
--   Fenchel biconjugate $f^{**}$
-- statement:
--   The **Fenchel biconjugate**: the conjugate applied twice.
--
--   For $f : \mathbb{R}^n \to \mathbb{R}$ with conjugate $f^{*}(y) = \sup_x(\langle x,y\rangle - f(x))$, the biconjugate is
--
--   $$f^{**}(x) \;=\; \sup_{y \in \mathbb{R}^n}\bigl(\langle x, y\rangle - f^{*}(y)\bigr) \;\in\; [-\infty,+\infty] .$$
--
--   By construction $f^{**}$ is the pointwise supremum of all affine functions lying below $f$ — the *closed convex envelope* of $f$ — so $f^{**} \le f$ always, with equality exactly for closed convex $f$. That equality is the Fenchel–Moreau theorem, proved in this mission.
--
--   The biconjugate is how one says precisely what information a dual description retains: passing to the dual and back recovers a convex function exactly and replaces a nonconvex one by its convex envelope, which is also the mechanism behind the duality gap of a nonconvex problem.
--
--   **Formalization Note** The definition is `EReal`-valued and subtracts the `EReal`-valued conjugate, so the arithmetic is that of the extended reals; it is stated for finite-valued `f`, matching `fenchelConjugate`. Source: B&V §3.3.2, p. 94.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 94, §3.3.2 (the conjugate of the conjugate)

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Fenchel biconjugate** `f**(x) = sup_y (⟪x,y⟫ − f*(y))` (B&V §3.3.2). -/
noncomputable def fenchelBiconjugate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ y : EuclideanSpace ℝ (Fin n), (((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y)

end ConvexOptimization


