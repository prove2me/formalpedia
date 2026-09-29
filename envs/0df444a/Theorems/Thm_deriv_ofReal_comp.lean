-- Prove2me | Theorems.Thm_deriv_ofReal_comp
-- name    : deriv.ofReal_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:35:10.112564+00:00
-- url     : https://prove2.me/theorems/e4010ad8-49c1-4afc-aed5-6b7e4c586581
-- title:
--   Derivative commutes with the coercion $\mathbb{R} \hookrightarrow \mathbb{C}$: $\dfrac{d}{dy}\,\bigl(f(y) : \mathbb{C}\bigr) = f'(y)$
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ be any real function and let $z \in \mathbb{R}$. Consider the complex-valued function obtained by post-composing $f$ with the embedding of $\mathbb{R}$ into $\mathbb{C}$, i.e. $y \mapsto (f(y) : \mathbb{C})$. Then its derivative at $z$ is the coercion of the real derivative:
--
--   $$\frac{d}{dy}\Bigl(y \mapsto \bigl(f(y) : \mathbb{C}\bigr)\Bigr)(z) \;=\; f'(z),$$
--
--   where the right-hand side is the real derivative of $f$ at $z$, viewed as a complex number. No differentiability hypothesis is needed: the coercion $\mathbb{R} \to \mathbb{C}$ is a continuous linear isometric embedding, so it maps derivatives to derivatives, and when $f$ is not differentiable at $z$ both sides are the junk value $0$.
--
--   This is a small but ubiquitous bridging lemma for computations that mix real-variable calculus with complex-valued integrands, as happens throughout the Fourier/Mellin and contour-integration infrastructure of the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L72-L78

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

theorem deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by sorry
