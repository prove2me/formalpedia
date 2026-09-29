-- Prove2me | Theorems.Thm_DifferentiableAt_ofReal_comp_iff
-- name    : DifferentiableAt.ofReal_comp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:32:27.029713+00:00
-- url     : https://prove2.me/theorems/24b6236e-673e-4be1-abcc-85f65def3d8a
-- title:
--   Pointwise differentiability is equivalent for $f$ and its complexification
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ and $z \in \mathbb{R}$. Then the complexification of $f$ is differentiable at $z$ if and only if $f$ is:
--   $$\text{DifferentiableAt}_{\mathbb{R}} \bigl(y \mapsto (f(y):\mathbb{C})\bigr)\, z \iff \text{DifferentiableAt}_{\mathbb{R}}\, f \, z.$$
--
--   The nontrivial direction recovers a real derivative from the complexified map: since the function takes values in the real axis, its derivative at $z$ is a real number, and $f$ inherits differentiability with that derivative.
--
--   This is the pointwise version of the global equivalence for complexified real functions. In the PNT+ development it is used to move differentiability hypotheses freely between the real-valued smoothing functions and their complex-valued appearances inside Mellin and Perron integrands.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L62-L66

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
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

theorem DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by sorry
