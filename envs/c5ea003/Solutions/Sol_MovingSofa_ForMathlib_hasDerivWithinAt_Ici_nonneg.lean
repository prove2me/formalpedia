-- Prove2me | solution 1 for MovingSofa.ForMathlib.hasDerivWithinAt_Ici_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:28:30.429575+00:00
-- url     : https://prove2.me/submissions/557d5ad2-65c7-4a6a-9820-804253df23d9

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_MovingSofa_ForMathlib_one_mem_posTangentConeAt_Ici

set_option autoImplicit false

open MovingSofa.ForMathlib

theorem solution {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by
  simpa using h.hasFDerivWithinAt_nonneg hf (one_mem_posTangentConeAt_Ici a)
