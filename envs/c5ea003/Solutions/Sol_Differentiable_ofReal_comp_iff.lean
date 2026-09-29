-- Prove2me | solution 1 for Differentiable.ofReal_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:03:12.724595+00:00
-- url     : https://prove2.me/submissions/715b4975-fae4-4852-9cfe-316c7a394c28

/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Theorems.Thm_DifferentiableAt_ofReal_comp_iff

/-!
### Auxiliary lemmas
-/

open Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

open Differentiable in
theorem solution {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

