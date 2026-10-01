-- Prove2me | solution 1 for MovingSofa.ForMathlib.hasDerivWithinAt_Iic_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:29:01.74093+00:00
-- url     : https://prove2.me/submissions/e160f131-c912-403c-a717-9498670072c4

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_MovingSofa_ForMathlib_neg_one_mem_posTangentConeAt_Iic

set_option autoImplicit false

open MovingSofa.ForMathlib

theorem solution {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 :=
  neg_nonneg.1 <| by
    simpa using h.hasFDerivWithinAt_nonneg hf (neg_one_mem_posTangentConeAt_Iic a)
