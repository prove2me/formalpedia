-- Prove2me | Theorems.Thm_Differentiable_ofReal_comp_iff
-- name    : Differentiable.ofReal_comp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:32:36.684889+00:00
-- url     : https://prove2.me/theorems/c6dd7683-163c-4020-9a59-bf75e8781a6c
-- title:
--   Real differentiability is equivalent for $f$ and its complexification $x \mapsto (f(x):\mathbb{C})$
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ be a real function, and consider its complexification $\tilde f : \mathbb{R} \to \mathbb{C}$, $\tilde f(y) = f(y)$ regarded as a complex number via the canonical embedding $\mathbb{R} \hookrightarrow \mathbb{C}$. Then
--   $$\tilde f \text{ is differentiable (over } \mathbb{R}\text{) everywhere} \iff f \text{ is differentiable everywhere}.$$
--
--   The forward direction extracts real differentiability from the complexified map (the derivative is automatically real-valued), while the converse composes $f$ with the $\mathbb{R}$-linear isometric embedding $\mathbb{R} \to \mathbb{C}$.
--
--   This is a convenient glue lemma between real and complex analysis: in the PNT+ project one constantly passes between real-variable estimates (for mollifiers, Chebyshev functions, Mellin integrands) and their complex-valued incarnations inside contour integrals, and this equivalence lets differentiability hypotheses be transported in either direction without loss.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L68-L70

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

theorem Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f := by sorry
