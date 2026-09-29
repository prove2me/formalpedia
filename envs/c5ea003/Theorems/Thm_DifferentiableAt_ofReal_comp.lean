-- Prove2me | Theorems.Thm_DifferentiableAt_ofReal_comp
-- name    : DifferentiableAt.ofReal_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:32:08.14928+00:00
-- url     : https://prove2.me/theorems/5f22f7f3-d60b-4aff-a28d-912d4783707f
-- title:
--   Complexifying a real-differentiable function preserves differentiability at a point
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ and $z \in \mathbb{R}$. If $f$ is differentiable at $z$, then the complexified function
--   $$y \mapsto (f(y) : \mathbb{C}),$$
--   obtained by post-composing $f$ with the canonical embedding $\mathbb{R} \hookrightarrow \mathbb{C}$, is differentiable over $\mathbb{R}$ at $z$.
--
--   The proof direction is the easy one: the embedding $\mathbb{R} \to \mathbb{C}$ is an $\mathbb{R}$-linear isometry, so it transports differentiability.
--
--   This pointwise transport lemma lets real-variable computations (with mollifiers, weight functions, and Chebyshev-type sums in the PNT+ project) be injected into complex-valued integrands without re-proving differentiability, and is a small reusable bridge between the real and complex API.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L42-L44

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

theorem DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z := by sorry
