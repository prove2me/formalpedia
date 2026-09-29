-- Prove2me | Theorems.Thm_Complex_differentiableAt_ofReal
-- name    : Complex.differentiableAt_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:57:23.324302+00:00
-- url     : https://prove2.me/theorems/f827f867-3e49-40a0-9c2f-675de6cd7d33
-- title:
--   The embedding $\mathbb{R} \hookrightarrow \mathbb{C}$ is differentiable at every point
-- statement:
--   For every real number $x$, the canonical inclusion map
--   $$\iota : \mathbb{R} \to \mathbb{C}, \qquad \iota(t) = t + 0i$$
--   is differentiable at $x$ in the sense of real ($\mathbb{R}$-linear) differentiability (Lean's `DifferentiableAt ℝ`).
--
--   The inclusion is an $\mathbb{R}$-linear (indeed isometric) map, so it is everywhere differentiable with derivative the inclusion itself; the lemma packages this as a `DifferentiableAt` statement at an arbitrary point.
--
--   This tiny bridging lemma is needed constantly when doing calculus on real-parametrized paths in $\mathbb{C}$ — e.g. differentiating integrands like $t \mapsto f(\sigma + it)$ along vertical lines or the edges of rectangular contours — where the chain rule requires knowing that the real-to-complex coercion is differentiable.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L22-L23

/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
### Auxiliary lemmas
-/

open Complex

theorem Complex.differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x := by sorry
