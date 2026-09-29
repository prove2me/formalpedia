-- Prove2me | Theorems.Thm_deriv_comp_ofReal
-- name    : deriv.comp_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:35:00.654953+00:00
-- url     : https://prove2.me/theorems/9fc88a8c-2fe6-4db7-a741-b48e7f5c1f2a
-- title:
--   Real-restriction of a complex derivative: $\dfrac{d}{dx}\, e(x)\big|_{\mathbb{R}} = e'(x)$ for $e$ complex-differentiable
-- statement:
--   Let $e : \mathbb{C} \to \mathbb{C}$ be a function that is complex-differentiable at a real point $z \in \mathbb{R}$ (viewed inside $\mathbb{C}$). Consider the restriction of $e$ to the real line, i.e. the function $x \mapsto e(x)$ of a real variable $x$ (with $x$ coerced into $\mathbb{C}$). Then its real-variable derivative at $z$ agrees with the complex derivative of $e$ at $z$:
--
--   $$\frac{d}{dx}\Bigl(x \mapsto e(x)\Bigr)(z) \;=\; e'(z).$$
--
--   This is the chain rule for the composition of $e$ with the inclusion $\mathbb{R} \hookrightarrow \mathbb{C}$, whose derivative is $1$. Though elementary, it is a frequently needed glue lemma: computations in the PNT+ project constantly pass between complex-analytic derivative facts (about $\zeta$, powers $t^{-s}$, Mellin integrands) and the real-variable derivatives that appear inside interval integrals and the one-dimensional fundamental theorem of calculus.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L34-L36

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

theorem deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z := by sorry
